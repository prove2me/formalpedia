-- Prove2me | Theorems.Thm_ConleyZehnder_czValue_existsUnique
-- name    : ConleyZehnder.czValue_existsUnique
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:20:44.374965+00:00
-- url     : https://prove2.me/theorems/1cabd740-6851-40b1-aa04-5233cca0b320
-- title:
--   $\mu_{CZ}(\psi)=\deg(\hat\rho^2\circ\tilde\psi)$ exists and does not depend on the extension
-- statement:
--   Let $\psi\in\mathrm{SP}(n)$. There is exactly one integer $k$ with the following property: for some path $\chi:[0,1]\to\mathrm{Sp}^*(2n)$ with $\chi(0)=\psi(1)$ and $\chi(1)\in\{W^+,W^-\}$, and some continuous arguments $\theta_1$ of $\hat\rho\circ\psi$ and $\theta_2$ of $\hat\rho\circ\chi$,
--   $$2\big((\theta_1(1)-\theta_1(0))+(\theta_2(1)-\theta_2(0))\big)=2\pi k .$$
--
--   So the degree of $\hat\rho^2$ along the concatenated path $\tilde\psi$ exists and is the same for every admissible extension; this integer is $\mu_{CZ}(\psi)$.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Section 2, paragraph before Definition 7, p. 6; Corollary 12, p. 8; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt §2, before Definition 7: every `ψ ∈ SP(n)` has an extension `ψ̃` through `Sp*`
to `W⁺` or `W⁻`, and the degree `deg(ρ̂² ∘ ψ̃)` does not depend on the extension. -/
theorem czValue_existsUnique {n : ℕ} (ψ : C(unitInterval, Mat n)) (hψ : ψ ∈ SP n) :
    ∃! k : ℤ, IsCZValue ψ k := by sorry

end ConleyZehnder
