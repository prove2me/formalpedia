-- Prove2me | Theorems.Thm_ConleyZehnder_rhoHat_diamond
-- name    : ConleyZehnder.rhoHat_diamond
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T10:12:27.003615+00:00
-- url     : https://prove2.me/theorems/10217c90-f9f9-4e58-8dd8-7ea32e1050cb
-- title:
--   ρ̂ is multiplicative under the block-diagonal sum ⋄
-- statement:
--   Let $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$ be the normalized complex determinant of the complex-linear part $C_A=\tfrac12(A-J_0AJ_0)$ of a real $2n\times 2n$ matrix $A$ (Gutt, formula (9)), and let $A'\diamond A''$ be the block-diagonal sum of a $2n'\times 2n'$ matrix $A'$ and a $2n''\times 2n''$ matrix $A''$, acting on $\mathbb R^{2(n'+n'')}$ by $(q',q'',p',p'')\mapsto$ ($A'$ on $(q',p')$, $A''$ on $(q'',p'')$) (Gutt, Proposition 8 (4)).
--
--   For all real matrices $A'$ and $A''$,
--   $$\det_{\mathbb C}C_{A'\diamond A''}=\det_{\mathbb C}C_{A'}\cdot\det_{\mathbb C}C_{A''}\qquad\text{and}\qquad\hat\rho(A'\diamond A'')=\hat\rho(A')\,\hat\rho(A'').$$
--
--   This is the compatibility of the function $\hat\rho$, which defines the Conley–Zehnder index, with the product $\diamond$ of symplectic matrices. It is used for the product property $\mu_{CZ}(\psi'\diamond\psi'')=\mu_{CZ}(\psi')+\mu_{CZ}(\psi'')$ (Gutt, Proposition 8 (4)).
--
--   Formalization note: `complexLinearDet`, `rhoHat`, `diamond` and `Mat n` come from the definition module `ConleyZehnder_Setting`; `complexLinearDet A` is the determinant of the complex $n\times n$ matrix $X+iY$, where $C_A=\begin{pmatrix}X&-Y\\Y&X\end{pmatrix}$. No symplecticity is assumed.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (4) and formula (9)

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- `det_ℂ C_{A ⋄ B} = det_ℂ C_A · det_ℂ C_B` and `ρ̂(A ⋄ B) = ρ̂(A) ρ̂(B)`. -/
theorem rhoHat_diamond {n' n'' : ℕ} (A : Mat n') (B : Mat n'') :
    complexLinearDet (diamond A B) = complexLinearDet A * complexLinearDet B ∧
      rhoHat (diamond A B) = rhoHat A * rhoHat B := by sorry

end ConleyZehnder
