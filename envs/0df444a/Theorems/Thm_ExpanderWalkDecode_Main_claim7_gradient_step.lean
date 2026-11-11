-- Prove2me | Theorems.Thm_ExpanderWalkDecode_Main_claim7_gradient_step
-- name    : ExpanderWalkDecode.Main.claim7_gradient_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:24:31.760931+00:00
-- url     : https://prove2.me/theorems/e86bdbe1-8c4a-4a2a-ad1e-b615b935bd66
-- title:
--   Claim 7 (Gradient Step Subroutine) — $\Gamma(P,Q)\le\min_V\Gamma(P,V)+\rho^2/2$ in time $\tilde O(N)\,\mathrm{poly}\cdot\log(1/\delta)$
-- statement:
--   There are absolute constants $C>0$, $K$, $c$, $p$ and one randomized program with the following property. Given the walk structure, a received word $Y\in\{\pm1\}$ on the $N$ code coordinates, $0<\rho\le1$, $\delta>0$, $R\ge|\mathrm{WRW}^{\le t}_s(a)|$ for all $a$, and Gram vectors (of any dimension $d$) of some $P\in\mathcal E$, the program halts within
--   $$K\,(N+|A|+qsm+1)\,(d+1)\,(\log_2(N+2))^p\Big(\frac{(R+1)(t+1)}{\rho}\Big)^{c}\log(2+1/\delta)$$
--   steps, always outputs $\Delta$-dimensional Gram vectors of some $Q\in\mathcal E$, where $\Delta=\lceil C(12+64\alpha)^2\rho^{-4}\log(2+NR)\rceil$ and $\alpha=10240R^2(t+1)^3/\rho^8$, and with probability at least $1-\delta$
--   $$\Gamma(P,Q)\le\min_{V\in\mathcal E}\Gamma(P,V)+\frac{\rho^2}2 .$$
--
--   It is the gradient-step oracle of the vector-recovery loop (Figure 2).
--
--   Differences from the source:
--   - generalization: the paper's walk structure (graphs of Proposition 3, base code of Proposition 1) → any outer graph with ports F_2^m, any inner Cayley graph on (F_2^m)^s, any t, any base code and embedding; reason: the statement uses no expansion property; specializes to the paper's structure
--   - reading: Õ(N)·poly(1/ε) → K(N + |A| + qsm + 1)·(d+1)·(log₂(N+2))^p·((R+1)(t+1)/ρ)^c with absolute constants, N the number of code coordinates; reason: for a general walk structure the input size and R, t, 1/ρ are the parameters that the paper bounds by N and poly(1/ε); the factor d+1 charges input vector coordinates, and the source dimension D is poly(1/ε) times a polylogarithm in N
--   - reading: E_{a∼A} E_{⃗a,⃗a′∼WRW^{≤t}_s(a)} in G(P) → ⃗a, ⃗a′ drawn uniformly from the set WRW^{≤t}_s(a); reason: the source gives no other law on walks of mixed lengths; Claim 11's proof bounds sums over WRW^{≤t}_s(a) by R times this average
--   - reading: Δ = O((12+64α)² log(N)/ρ⁴) → Δ = ⌈C(12+64α)²ρ^{-4} log(2+NR)⌉; reason: the proof applies Proposition 6 with k = |WRW^{≤t}_s| ≤ NR; regularized logarithm as in Proposition 6
--   - reading: outputs Gram vectors of Q ∈ E such that, with probability ≥ 1−δ, … → Q ∈ E on every run; the inequality with probability ≥ 1−δ; reason: the stronger of the two readings
--   - encoding: log(1/δ); min_{V∈E} → log(2+1/δ); ∀ V ∈ E; reason: same for small δ and defined for all δ > 0; the minimum is attained on the compact E
--   - generalization: a received word on the support set of wide replacement walks → an arbitrary received sign word on the full latent-coordinate space; reason: a source word pulls back along the walk map; all copies of a support coordinate then have the same received sign. The extension keeps the latent sampling law and charges every coordinate
--   - reading: algorithmic running time, without an explicit machine specification → the mission machine: a unit-cost real RAM with √, natural logarithm, fair coins and an exact symmetric eigendecomposition charged d³+1; reason: the source thresholds eigenvalues exactly (Figure 3), takes exact top eigenvectors (Figure 4) and sets parameters by logarithmic formulas (Δ, ℓ), counting these steps as polynomial work; an exact eigenvalue threshold is meaningful only in exact real arithmetic, so this is the model the source computes in; the cubic charge is one polynomial cost for the step the source calls immediate
-- source:
--   Silas Richelson, Sourya Roy, Madhur Tulsiani, Decoding Expander Walk Codes up to the Johnson Bound in Near-Linear Time, STOC 2027 submission #1736 (October 2026), p. 12 (PDF p. 15), §4.1, Claim 7; proof p. 28 (PDF p. 31)

import Mathlib
import Definitions.Def_ExpanderWalkDecode_Main_Encoding

namespace ExpanderWalkDecode.Main

open scoped Matrix

/-- Claim 7 (Gradient Step Subroutine) (§4.1, p. 12; proof in Appendix C.1): there are absolute
constants and one randomized program that, given the walk structure, `Y ∈ {±1}^{WRW^t_s}`,
`0 < ρ ≤ 1`, `δ > 0`, `R ≥ |WRW^{≤t}_s(a)|` and Gram vectors of some `P ∈ E` (any dimension `d`),
runs in time `Õ(N) poly(R, t, 1/ρ) log(1/δ)` and always outputs `Δ`-dimensional Gram vectors of
some `Q ∈ E`, with `Γ(P, Q) ≤ min_{V ∈ E} Γ(P, V) + ρ²/2` with probability at least `1 - δ`
(`α`, `Δ` as in §4.1). -/
theorem claim7_gradient_step :
    ∃ (C K c : ℝ) (p : ℕ) (P : Program), 0 < C ∧ Admissible P ∧
      ∀ (nA m s q t : ℕ) (G : RotGraph (Fin nA) (Fin m → ZMod 2)) (u : Fin q → Inner m s) (R d : ℕ)
        (Y : Latent (Fin nA) m s q t → ℝ) (ρ δ : ℝ) (x : WIdx G u t → Fin d → ℝ)
        (l : List (WIdx G u t)),
        (∀ z, Y z = 1 ∨ Y z = -1) → 0 < ρ → ρ ≤ 1 → 0 < δ →
        (∀ a, (fromW G u t a).card ≤ R) → Enumerates l → gram G u t x ∈ Ell G u t →
        ∃ T : ℕ,
          (T : ℝ) ≤ K * ((Fintype.card (Latent (Fin nA) m s q t) : ℝ) + nA + q * s * m + 1)
            * ((d : ℝ) + 1) * Real.logb 2 ((Fintype.card (Latent (Fin nA) m s q t) : ℝ) + 2) ^ p
            * (((R : ℝ) + 1) * ((t : ℝ) + 1) / ρ) ^ c * Real.log (2 + 1 / δ) ∧
          HaltsWithin P (structInput G u t [(R : ℤ), (d : ℤ)] (fun _ => 0) [ρ, δ] (latentBank Y)
            (vectorRecords l x)) T ∧
          (∀ bits : Fin T → Bool, ∃ y : WIdx G u t →
              Fin (deltaDim C (alphaP R t ρ) ρ (Fintype.card (Latent (Fin nA) m s q t)) R) → ℝ,
            EncodesVectors (run P (extendBits bits) (structInput G u t [(R : ℤ), (d : ℤ)]
              (fun _ => 0) [ρ, δ] (latentBank Y) (vectorRecords l x)) T).output y ∧
            gram G u t y ∈ Ell G u t) ∧
          1 - δ ≤ successProb P (structInput G u t [(R : ℤ), (d : ℤ)] (fun _ => 0) [ρ, δ]
              (latentBank Y) (vectorRecords l x)) T (fun out =>
            ∃ y : WIdx G u t →
                Fin (deltaDim C (alphaP R t ρ) ρ (Fintype.card (Latent (Fin nA) m s q t)) R) → ℝ,
              EncodesVectors out y ∧ ∀ V ∈ Ell G u t,
                Gamma G u t (alphaP R t ρ) Y ρ (gram G u t x) (gram G u t y) ≤
                  Gamma G u t (alphaP R t ρ) Y ρ (gram G u t x) V + ρ ^ 2 / 2) := by sorry

end ExpanderWalkDecode.Main
