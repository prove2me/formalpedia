-- Prove2me | Theorems.Thm_EllsbergLearning_lemma_4_1_symmetric
-- name    : EllsbergLearning.lemma_4_1_symmetric
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:13.091953+00:00
-- url     : https://prove2.me/theorems/20f7278c-5073-407c-9b8f-3cd38620d7f6
-- title:
--   Lemma 4.1 (36)–(37), p.20 — symmetry of the critical values and the cut-off $u_2^{**}$ (corrected: $u_2^{**}$ of (34))
-- statement:
--   Assume the standing assumptions and payoff symmetry $u_{01}=u_{10}$. Let $(\underline\pi,\overline\pi,\tilde z)$ be the indifference point and $(r^R,r^l)$ the solution of (32). Then
--
--   1. (36): $\underline\pi+\overline\pi=1=r^l+r^R$;
--   2. (37): for every solution $(r^l_1,r^l_2)$ of (31), $r^l_1\le\overline\pi\iff u_2\ge u_2^{**}$; for every solution $(r^R_1,r^R_2)$ of (30), $r^R_1\ge\underline\pi\iff u_2\ge u_2^{**}$. In particular $r^l_1\le\overline\pi\iff r^R_1\ge\underline\pi\iff u_2\ge u_2^{**}$ when both exist.
--
--   The cut-off $u_2^{**}$ separates the two cases (a.i) and (a.ii) of Theorem 4.2.
--
--   Differences from the source:
--   - correction: (34): $u_2^{**}=\tfrac{\hat c}{2}[\cdots]+\tfrac{u_{00}-u_{01}}{2}$ → $u_2^{**}=\tfrac{\hat c}{2}[\cdots]+\tfrac{u_{00}+u_{01}}{2}$; reason: the printed value contradicts (37) and the paper's identity $u_2^{**}=g_1(\overline\pi;C_1,C_2)$ (p.26): in the Ellsberg instance $\alpha=1/8$, $c=0.01$, $\sigma=1$, $\epsilon=0.04$ (all assumptions hold) the printed $u_2^{**}\approx0.126<u_2=1/2$ while $r_1^l=\hat r\approx0.5244>\overline\pi=0.52$; the corrected value $\approx0.5011$ equals $g_1(\overline\pi)$ and $v_0$ of (26)
--   - reading: (37) $r_1^l\le\overline\pi\iff r_1^R\ge\underline\pi\iff u_2\ge u_2^{**}$ (after "if $u_2\ge u_2^{**}$ ... also") → for every solution of (31), $r_1^l\le\overline\pi\iff u_2\ge u_2^{**}$, and for every solution of (30), $r_1^R\ge\underline\pi\iff u_2\ge u_2^{**}$; reason: under the hypothesis $u_2\ge u_2^{**}$ the equivalence would be empty; the proof (p.31) and Theorem 3.1's proof use it where $u_2<u_2^{**}$
--   - encoding: posteriors $\underline m_t,\overline m_t$ by Bayesian updating (Liptser–Shiryaev, Theorem 9.1) → the closed form (12)–(13), as a function of $(t,z)$; reason: the paper's own formula; same objects
--   - generalization: a trajectory $(\tilde z_t)_{t\ge0}$ → a function $\tilde z:\mathbb R\to\mathbb R$ with the defining identities for every real $t$; reason: the closed forms extend to all real $t$; the paper's trajectory is the restriction to $t\ge0$, and uniqueness on $\mathbb R$ implies uniqueness on $[0,\infty)$
-- source:
--   Epstein & Ji, Optimal Learning under Robustness and Time-Consistency, arXiv:1708.01890v2, Lemma 4.1, (36)–(37), p.20

import Definitions.Def_EllsbergLearning_CriticalValues

namespace EllsbergLearning

/-- Lemma 4.1, (36)–(37) (Epstein & Ji, arXiv:1708.01890v2, p.20): under the standing assumptions
of §3.1 and payoff symmetry `u₀₁ = u₁₀`, with `(π̲, π̄, z̃)` the indifference point and `(rᴿ, rˡ)`
the solution of (32),

1. (36): `π̲ + π̄ = 1 = rˡ + rᴿ`;
2. (37): for every solution `(r₁ˡ, r₂ˡ)` of (31), `r₁ˡ ≤ π̄ ⇔ u₂ ≥ u₂**`, and for every solution
   `(r₁ᴿ, r₂ᴿ)` of (30), `r₁ᴿ ≥ π̲ ⇔ u₂ ≥ u₂**` (so `r₁ˡ ≤ π̄ ⇔ r₁ᴿ ≥ π̲ ⇔ u₂ ≥ u₂**`), with `u₂**`
   of (34), corrected. -/
theorem lemma_4_1_symmetric (p : Params) (hp : p.Valid) (hsym : p.PayoffSymmetry)
    (πL πU : ℝ) (zt : ℝ → ℝ) (hind : p.IsIndifference πL πU zt) (rR rl : ℝ)
    (h32 : p.Solves32 πL πU rR rl) :
    πL + πU = 1 ∧ rl + rR = 1 ∧
      (∀ r1l r2l : ℝ, p.Solves31 r1l r2l → (r1l ≤ πU ↔ p.u2StarStar πU rl ≤ p.u₂)) ∧
      (∀ r1R r2R : ℝ, p.Solves30 r1R r2R → (πL ≤ r1R ↔ p.u2StarStar πU rl ≤ p.u₂)) := by sorry

end EllsbergLearning
