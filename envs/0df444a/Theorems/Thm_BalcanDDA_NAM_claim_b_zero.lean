-- Prove2me | Theorems.Thm_BalcanDDA_NAM_claim_b_zero
-- name    : BalcanDDA.NAM.claim_b_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:37:46.55519+00:00
-- url     : https://prove2.me/theorems/fe8ddb82-c8a3-4e90-b98d-8f9c61072faf
-- title:
--   Proof of Theorem 5.2, first claim — if $b_\ell = 0$ then $u_\rho(v^{(\ell)}) = \epsilon$
-- statement:
--   Let $n$ be the number of agents, $m\ge 2$ the number of alternatives, $N=\lfloor n/2\rfloor$, and $\varepsilon\in(0,\tfrac12)$. Let $v^{(\ell)}$ ($\ell\in[N]$) be the valuation profiles and, for a bit vector $b\in\{0,1\}^N$, let $\rho$ be the parameter vector constructed in the proof of Theorem 5.2. Let $\psi$ be any outcome rule that returns a maximizer of the weighted value $\sum_i\rho[i]v_i(j)$, and $u_\rho(v)=\sum_i v_i(\psi_\rho(v))$ the welfare of its outcome. Then for every $\ell\in[N]$,
--   $$b_\ell=0\ \Longrightarrow\ u_\rho\bigl(v^{(\ell)}\bigr)=\varepsilon .$$
--
--   Together with the second claim ($b_\ell=1\Rightarrow u_\rho(v^{(\ell)})=1$), this shows that the threshold $\tfrac12$ separates the two values on every profile, which is how the profiles $v^{(1)},\dots,v^{(N)}$ are shattered.
--
--   **Formalization Note** `welfare ψ (paramOf n b) (profile n m ε ℓ) = ε` for `b ℓ = false`, for every `ψ` satisfying `IsArgmaxSelector ψ`; the paper's first and second alternatives are `0` and `1`, and alternatives beyond the second (when $m>2$) carry value $0$ in every profile. The paper takes $m=2$; the claim is stated for every $m\ge 2$.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 24, proof of Theorem 5.2, paragraph "We claim that if b_ℓ = 0, then u_ρ(v^(ℓ)) = ϵ"

import Mathlib
import Definitions.Def_BalcanDDA_NAM_Model
import Definitions.Def_BalcanDDA_NAM_Construction

namespace BalcanDDA.NAM

/-- Proof of Theorem 5.2 (Balcan et al., arXiv:1908.02894v4, p. 24), first claim: if
`b_ℓ = 0` then `u_ρ(v^(ℓ)) = ε`, for the constructed `ρ = paramOf n b` and
`v^(ℓ) = profile n m ε ℓ`, for every argmax outcome rule `ψ` and `m ≥ 2` alternatives. -/
theorem claim_b_zero (n m : ℕ) (hm : 2 ≤ m) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m) (hψ : IsArgmaxSelector ψ)
    (b : Fin (n / 2) → Bool) (ℓ : Fin (n / 2)) (hb : b ℓ = false) :
    welfare ψ (paramOf n b) (profile n m ε ℓ) = ε := by sorry

end BalcanDDA.NAM
