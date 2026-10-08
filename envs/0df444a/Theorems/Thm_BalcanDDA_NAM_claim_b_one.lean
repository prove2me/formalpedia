-- Prove2me | Theorems.Thm_BalcanDDA_NAM_claim_b_one
-- name    : BalcanDDA.NAM.claim_b_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:37:56.890294+00:00
-- url     : https://prove2.me/theorems/38816788-b2ca-4c7f-93d3-e1a4dfed9ded
-- title:
--   Proof of Theorem 5.2, second claim — if $b_\ell = 1$ then $u_\rho(v^{(\ell)}) = 1$
-- statement:
--   Let $n$ be the number of agents, $m\ge 2$ the number of alternatives, $N=\lfloor n/2\rfloor$, and $\varepsilon\in(0,\tfrac12)$. Let $v^{(\ell)}$ ($\ell\in[N]$) be the valuation profiles and, for a bit vector $b\in\{0,1\}^N$, let $\rho$ be the parameter vector constructed in the proof of Theorem 5.2. Let $\psi$ be any outcome rule that returns a maximizer of the weighted value $\sum_i\rho[i]v_i(j)$, and $u_\rho(v)=\sum_i v_i(\psi_\rho(v))$ the welfare of its outcome. Then for every $\ell\in[N]$,
--   $$b_\ell=1\ \Longrightarrow\ u_\rho\bigl(v^{(\ell)}\bigr)=1 .$$
--
--   With the first claim ($b_\ell=0\Rightarrow u_\rho(v^{(\ell)})=\varepsilon<\tfrac12$), this realizes every bit pattern $b$ with the witnesses $z^{(\ell)}=\tfrac12$.
--
--   **Formalization Note** `welfare ψ (paramOf n b) (profile n m ε ℓ) = 1` for `b ℓ = true`, for every `ψ` satisfying `IsArgmaxSelector ψ`; alternatives are 0-based and the claim is stated for every $m\ge2$ (the paper takes $m=2$).
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 24, proof of Theorem 5.2, paragraph "Next, we claim that if b_ℓ = 1, then u_ρ(v^(ℓ)) = 1"

import Mathlib
import Definitions.Def_BalcanDDA_NAM_Model
import Definitions.Def_BalcanDDA_NAM_Construction

namespace BalcanDDA.NAM

/-- Proof of Theorem 5.2 (Balcan et al., arXiv:1908.02894v4, p. 24), second claim: if
`b_ℓ = 1` then `u_ρ(v^(ℓ)) = 1`, for the constructed `ρ = paramOf n b` and
`v^(ℓ) = profile n m ε ℓ`, for every argmax outcome rule `ψ` and `m ≥ 2` alternatives. -/
theorem claim_b_one (n m : ℕ) (hm : 2 ≤ m) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (ψ : (Fin n → ℝ) → (Fin n → Fin m → ℝ) → Fin m) (hψ : IsArgmaxSelector ψ)
    (b : Fin (n / 2) → Bool) (ℓ : Fin (n / 2)) (hb : b ℓ = true) :
    welfare ψ (paramOf n b) (profile n m ε ℓ) = 1 := by sorry

end BalcanDDA.NAM
