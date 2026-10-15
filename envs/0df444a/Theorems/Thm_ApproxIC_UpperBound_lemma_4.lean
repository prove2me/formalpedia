-- Prove2me | Theorems.Thm_ApproxIC_UpperBound_lemma_4
-- name    : ApproxIC.UpperBound.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:28.11179+00:00
-- url     : https://prove2.me/theorems/1018ffd3-ac07-4fe3-b6a3-2be23e279e37
-- title:
--   Lemma 4, p. 20 — if ∆ ≥ 0 on [x, ν₀] then ∫_x^v̄ ∆⁺ = ∫_x^v̄ ∆ ≤ R(x) + 2(w(x) − x)
-- statement:
--   Assume the standing density assumptions, fix a path $(\mu,\nu_0,v^\star,w)$ and let $\lambda^\star$ be Lemma 2's dual solution. Define the dual virtual value
--   $$\Delta(v)=vf(v)-\dot w(v)\,(w(v)-v)\,\lambda^\star(w(v))\,\mathbf 1_{\{v\in[0,\nu_0]\}} .$$
--   If $\Delta(v)\ge 0$ for all $v\in[x,\nu_0]$, for some $x\in[0,\nu_0)$, then
--   $$\int_x^{\bar v}\Delta(v)^+\,dv=\int_x^{\bar v}\Delta(v)\,dv\le R(x)+2\,(w(x)-x),$$
--   where $R(x)=x\,\bar F(x)$.
--
--   In classical mechanism design the integral of the virtual value times the density over $[x,\bar v]$ equals $R(x)$; here the dual virtual value costs at most the correction $2(w(x)-x)$.
--
--   **Formalization Note** The page prints "$\Phi_2(\lambda^{IC})=\int_x^{\bar v}\Delta(v)dv$", but $\Phi_2$ integrates $\Delta^+$ over $[0,\bar v]$, which differs whenever $\Delta>0$ somewhere on $[0,x)$. The statement here is the reading the proof (pp. 40–43) establishes and the proof of Theorem 1 (p. 48) uses: $\int_x^{\bar v}\Delta^+=\int_x^{\bar v}\Delta$, which holds because $\Delta\ge 0$ on $[x,\nu_0]$ and $\Delta=vf\ge 0$ on $(\nu_0,\bar v]$. $\lambda^\star$ is Lemma 2's explicit function.
-- source:
--   Balseiro, Besbes, Castro, Mechanism Design under Approximate Incentive Compatibility, arXiv:2103.03403v2 (2022), p. 20, Lemma 4 (proof pp. 40–43)

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Path

namespace ApproxIC.UpperBound

theorem lemma_4 (M : Model) (hM : M.Standing) (P : Path M) (x : ℝ) (hx : x ∈ Set.Ico 0 P.nu0)
    (hΔ : ∀ v ∈ Set.Icc x P.nu0, 0 ≤ Delta M P (lamStar M P) v) :
    (∫ v in x..M.vbar, max 0 (Delta M P (lamStar M P) v)) =
        ∫ v in x..M.vbar, Delta M P (lamStar M P) v ∧
      ∫ v in x..M.vbar, Delta M P (lamStar M P) v ≤ R M x + 2 * (P.w x - x) := by sorry

end ApproxIC.UpperBound
