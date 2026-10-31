-- Prove2me | Theorems.Thm_EllsbergLearning_boundary_maps
-- name    : EllsbergLearning.boundary_maps
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:21:02.240053+00:00
-- url     : https://prove2.me/theorems/40f5c389-47a9-4985-9f22-78fb3fa81d69
-- title:
--   §4, p.21 — $\underline m_t(\underline f(t,r))=r=\overline m_t(\overline f(t,r))$ and (38)
-- statement:
--   Under the standing assumptions:
--
--   1. for every $t$ and every $r\in(0,1)$, $\underline m_t(\underline f(t,r))=r=\overline m_t(\overline f(t,r))$;
--   2. for the indifference point $(\underline\pi,\overline\pi,\tilde z)$, every $t$ and all $r_1,r_2\in(0,1)$,
--   $$\overline f(t,r_1)\le\tilde z_t\iff r_1\le\overline\pi,\qquad \underline f(t,r_2)\ge\tilde z_t\iff r_2\ge\underline\pi.\quad(38)$$
--
--   So the stopping boundaries of Theorem 4.2 can be written either as signal levels or as posterior thresholds.
--
--   Differences from the source:
--   - encoding: posteriors $\underline m_t,\overline m_t$ by Bayesian updating (Liptser–Shiryaev, Theorem 9.1) → the closed form (12)–(13), as a function of $(t,z)$; reason: the paper's own formula; same objects
--   - generalization: times $t\ge 0$ → every real $t$ for the deterministic functions of $(t,z)$; reason: the closed forms (12)–(13) are defined for every real $t$; restricting to $t\ge0$ gives the paper's statement
--   - generalization: a trajectory $(\tilde z_t)_{t\ge0}$ → a function $\tilde z:\mathbb R\to\mathbb R$ with the defining identities for every real $t$; reason: the closed forms extend to all real $t$; the paper's trajectory is the restriction to $t\ge0$, and uniqueness on $\mathbb R$ implies uniqueness on $[0,\infty)$
--   - reading: for any $r_1$ and $r_2$ → for $r_1,r_2\in(0,1)$; reason: $\overline f,\underline f$ contain $\log(r/(1-r))$ and are defined only for probabilities $r\in(0,1)$
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, §4, p.21, (38)

import Definitions.Def_EllsbergLearning_Params

open Set

namespace EllsbergLearning

/-- The boundary maps and (38) (Epstein & Ji, arXiv:1708.01890v2, §4, p.21): under the standing
assumptions of §3.1,

1. `m̲_t(f̲(t, r)) = r = m̄_t(f̄(t, r))` for every `t` and every `r ∈ (0, 1)`;
2. for the indifference point `(π̲, π̄, z̃)` and all `r₁, r₂ ∈ (0, 1)`:
   `f̄(t, r₁) ≤ z̃_t ⇔ r₁ ≤ π̄` and `f̲(t, r₂) ≥ z̃_t ⇔ r₂ ≥ π̲`. -/
theorem boundary_maps (p : Params) (hp : p.Valid) :
    (∀ t r : ℝ, r ∈ Ioo (0 : ℝ) 1 → p.mLo t (p.fLo t r) = r ∧ p.mUp t (p.fUp t r) = r) ∧
      ∀ (πL πU : ℝ) (zt : ℝ → ℝ), p.IsIndifference πL πU zt →
        ∀ t r1 r2 : ℝ, r1 ∈ Ioo (0 : ℝ) 1 → r2 ∈ Ioo (0 : ℝ) 1 →
          (p.fUp t r1 ≤ zt t ↔ r1 ≤ πU) ∧ (zt t ≤ p.fLo t r2 ↔ πL ≤ r2) := by sorry

end EllsbergLearning
