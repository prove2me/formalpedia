-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_product
-- name    : ConleyZehnder.czIndex_product
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:22:16.289297+00:00
-- url     : https://prove2.me/theorems/1625a7e4-5c70-47a1-9f7d-c9cc14e95dbc
-- title:
--   Product property of the Conley–Zehnder index
-- statement:
--   Let $\psi'\in\mathrm{SP}(n')$ and $\psi''\in\mathrm{SP}(n'')$, and let $\psi'\diamond\psi''$ be the path $t\mapsto\psi'(t)\diamond\psi''(t)$ in $\mathrm{Sp}(2(n'+n''))$, where $\diamond$ is the block embedding $(q',p')\oplus(q'',p'')\mapsto(q',q'',p',p'')$. Then
--   $$\mu_{CZ}(\psi'\diamond\psi'')=\mu_{CZ}(\psi')+\mu_{CZ}(\psi'') .$$
--
--   **Formalization Note** The block-sum path is passed as a continuous path $\psi$ with $\psi(t)=\psi'(t)\diamond\psi''(t)$ for all $t$.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (4), p. 7; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, Proposition 8 (4), Product: `μ_CZ(ψ' ⋄ ψ'') = μ_CZ(ψ') + μ_CZ(ψ'')` for
`ψ' ∈ SP(n')`, `ψ'' ∈ SP(n'')`. -/
theorem czIndex_product {n' n'' : ℕ} (ψ₁ : C(unitInterval, Mat n')) (hψ₁ : ψ₁ ∈ SP n')
    (ψ₂ : C(unitInterval, Mat n'')) (hψ₂ : ψ₂ ∈ SP n'')
    (ψ : C(unitInterval, Mat (n' + n''))) (hψ : ∀ t, ψ t = diamond (ψ₁ t) (ψ₂ t)) :
    czIndex ψ = czIndex ψ₁ + czIndex ψ₂ := by sorry

end ConleyZehnder
