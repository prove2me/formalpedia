-- Prove2me | Theorems.Thm_CutwidthCircuitLB_appendix_A_sheppard
-- name    : CutwidthCircuitLB.appendix_A_sheppard
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:25:41.569222+00:00
-- url     : https://prove2.me/theorems/192f6edb-d547-4f86-9f75-0633b4b7ff6c
-- title:
--   Appendix A — Sheppard's formula: threshold $0$ separates with probability $\arccos(r)/\pi$, the worst threshold
-- statement:
--   Let $u, v \in \mathbb R^d$ be unit vectors and $\omega$ a standard Gaussian vector in $\mathbb R^d$, so that $\langle u, \omega\rangle$ and $\langle v, \omega\rangle$ are standard Gaussians with correlation $r = \langle u, v\rangle$. Then the threshold $0$ separates them with probability
--   $$
--   \Pr\big[\min(\langle u,\omega\rangle, \langle v,\omega\rangle) < 0 < \max(\langle u,\omega\rangle, \langle v,\omega\rangle)\big] = \frac{\arccos r}{\pi},
--   $$
--   and $0$ is the worst threshold: for every $t \in \mathbb R$, the probability that $t$ separates the two scores is at most this value.
--
--   This is the two-dimensional Gaussian estimate behind the bound on open vertices in Appendix A.
--
--   Differences from the source:
--   - encoding: two standard Gaussians of correlation r → the scores ⟨u, ω⟩, ⟨v, ω⟩ of unit vectors u, v ∈ ℝ^d under one standard Gaussian vector ω (Mathlib stdGaussian), r = ⟨u, v⟩; reason: Appendix A's scores k_e = ⟨y_e, ω⟩; every such pair arises this way with d = 2
--   - reading: 0 is the worst threshold → ∀ t, Pr[t separates] ≤ Pr[0 separates]; reason: the plain meaning of the sentence
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Appendix A, p.21 (citing Sheppard, Phil. Trans. R. Soc. A 192 (1899) 101–167)

import Mathlib
import Definitions.Def_CutwidthCircuitLB_Separates
open MeasureTheory ProbabilityTheory

namespace CutwidthCircuitLB

/-- **Appendix A, Sheppard's formula and the worst threshold** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Appendix A, p.21; Sheppard
1899): for unit vectors `u, v` and a standard Gaussian vector `ω`, the scores `⟨u, ω⟩, ⟨v, ω⟩` are
two standard Gaussians of correlation `r = ⟨u, v⟩`; the threshold `0` separates them with
probability `arccos(r)/π`, and `0` is the worst threshold: no threshold `t` separates them with
larger probability.

**Formalization Note** Two standard Gaussians of correlation `r` are encoded as two projections of
one standard Gaussian vector of `ℝ^d` (Mathlib's `stdGaussian`), as in Appendix A; every such pair
arises this way with `d = 2`. -/
theorem appendix_A_sheppard (d : ℕ) (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real
        {ω | Separates 0 (inner ℝ u ω) (inner ℝ v ω)} = Real.arccos (inner ℝ u v) / Real.pi ∧
      ∀ t : ℝ, (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          {ω | Separates t (inner ℝ u ω) (inner ℝ v ω)} ≤
        (stdGaussian (EuclideanSpace ℝ (Fin d))).real
          {ω | Separates 0 (inner ℝ u ω) (inner ℝ v ω)} := by sorry

end CutwidthCircuitLB
