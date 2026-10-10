-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_loop
-- name    : ConleyZehnder.czIndex_loop
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:22:32.182842+00:00
-- url     : https://prove2.me/theorems/b3d92c58-6bc6-4a23-8f33-2a5fa1df2fca
-- title:
--   Loop property of the Conley–Zehnder index
-- statement:
--   For every continuous loop $\varphi:[0,1]\to\mathrm{Sp}(2n)$ with $\varphi(0)=\varphi(1)=\mathrm{Id}$ and every $\psi\in\mathrm{SP}(n)$,
--   $$\mu_{CZ}(\varphi\psi)=\mu_{CZ}(\psi)+2\,\mu(\varphi),$$
--   where $\varphi\psi$ is the pointwise product $t\mapsto\varphi(t)\psi(t)$ and $\mu(\varphi)=\deg(\hat\rho\circ\varphi)$ is the Maslov index of the loop.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (5), p. 7; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, Proposition 8 (5), Loop: `μ_CZ(φψ) = μ_CZ(ψ) + 2 μ(φ)` for every loop `φ`
of symplectic matrices at `Id`. -/
theorem czIndex_loop (n : ℕ) : LoopAxiom (czIndex (n := n)) := by sorry

end ConleyZehnder
