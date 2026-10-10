-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_homotopy
-- name    : ConleyZehnder.czIndex_homotopy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:21:42.003184+00:00
-- url     : https://prove2.me/theorems/0b653531-443c-4d6c-939e-c90012421eb7
-- title:
--   Homotopy invariance of the Conley–Zehnder index
-- statement:
--   The Conley–Zehnder index $\mu_{CZ}:\mathrm{SP}(n)\to\mathbb{Z}$ is constant on each connected component of $\mathrm{SP}(n)$, where $\mathrm{SP}(n)$ carries the compact-open topology of $C([0,1],\mathbb{R}^{2n\times2n})$.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (2), p. 6; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, Proposition 8 (2), Homotopy: `μ_CZ` is constant on the components of
`SP(n)`. -/
theorem czIndex_homotopy (n : ℕ) : HomotopyAxiom (czIndex (n := n)) := by sorry

end ConleyZehnder
