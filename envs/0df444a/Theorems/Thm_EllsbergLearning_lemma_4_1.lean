-- Prove2me | Theorems.Thm_EllsbergLearning_lemma_4_1
-- name    : EllsbergLearning.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:11.625883+00:00
-- url     : https://prove2.me/theorems/b01873f9-93a1-485d-b8c2-4d68d2fd141d
-- title:
--   Lemma 4.1 (first part), p.20 — existence and uniqueness of the critical values (corrected: $u_2^{**}$ of (34))
-- statement:
--   Under the standing assumptions, with $(\underline\pi,\overline\pi,\tilde z)$ the indifference point:
--
--   1. (32) has a unique solution $(r^R,r^l)\in(0,1)^2$;
--   2. if $u_2\ge u_2^{**}$, then (30) and (31) each have a unique solution in $(0,1)^2$, and the solutions satisfy
--   $$r^l_2<r^l_1,\qquad r^R_1<r^R_2,\qquad \underline\pi<r^R,\qquad r^l<\overline\pi.$$
--
--   These critical values are the stopping boundaries of Theorem 4.2(a).
--
--   Differences from the source:
--   - correction: (34): $u_2^{**}=\tfrac{\hat c}{2}[\cdots]+\tfrac{u_{00}-u_{01}}{2}$ → $u_2^{**}=\tfrac{\hat c}{2}[\cdots]+\tfrac{u_{00}+u_{01}}{2}$; reason: the printed value contradicts (37) and the paper's identity $u_2^{**}=g_1(\overline\pi;C_1,C_2)$ (p.26): in the Ellsberg instance $\alpha=1/8$, $c=0.01$, $\sigma=1$, $\epsilon=0.04$ (all assumptions hold) the printed $u_2^{**}\approx0.126<u_2=1/2$ while $r_1^l=\hat r\approx0.5244>\overline\pi=0.52$; the corrected value $\approx0.5011$ equals $g_1(\overline\pi)$ and $v_0$ of (26)
--   - reading: unique solutions of (30)–(32) → unique in $(0,1)^2$; reason: $l$ and $\tilde l$ are defined for $r\in(0,1)$ only (p.20)
--   - encoding: posteriors $\underline m_t,\overline m_t$ by Bayesian updating (Liptser–Shiryaev, Theorem 9.1) → the closed form (12)–(13), as a function of $(t,z)$; reason: the paper's own formula; same objects
--   - generalization: a trajectory $(\tilde z_t)_{t\ge0}$ → a function $\tilde z:\mathbb R\to\mathbb R$ with the defining identities for every real $t$; reason: the closed forms extend to all real $t$; the paper's trajectory is the restriction to $t\ge0$, and uniqueness on $\mathbb R$ implies uniqueness on $[0,\infty)$
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, Lemma 4.1, p.20 (the clauses on (30)–(32)); (34), p.20

import Definitions.Def_EllsbergLearning_CriticalValues

namespace EllsbergLearning

/-- Lemma 4.1, the clauses on (30)–(32) (Epstein & Ji, arXiv:1708.01890v2, p.20): under the
standing assumptions of §3.1, with `(π̲, π̄, z̃)` the indifference point,

1. (32) has a unique solution `(rᴿ, rˡ)` in `(0, 1)²`;
2. if `u₂ ≥ u₂**` (with `u₂**` of (34), corrected), then (30) and (31) each have a unique solution
   in `(0, 1)²`, and the solutions satisfy `r₂ˡ < r₁ˡ`, `r₁ᴿ < r₂ᴿ`, `π̲ < rᴿ`, `rˡ < π̄`. -/
theorem lemma_4_1 (p : Params) (hp : p.Valid) (πL πU : ℝ) (zt : ℝ → ℝ)
    (hind : p.IsIndifference πL πU zt) :
    (∃! r : ℝ × ℝ, p.Solves32 πL πU r.1 r.2) ∧
      ∀ rR rl : ℝ, p.Solves32 πL πU rR rl → p.u2StarStar πU rl ≤ p.u₂ →
        (∃! r : ℝ × ℝ, p.Solves30 r.1 r.2) ∧ (∃! r : ℝ × ℝ, p.Solves31 r.1 r.2) ∧
          ∀ r1R r2R r1l r2l : ℝ, p.Solves30 r1R r2R → p.Solves31 r1l r2l →
            r2l < r1l ∧ r1R < r2R ∧ πL < rR ∧ rl < πU := by sorry

end EllsbergLearning
