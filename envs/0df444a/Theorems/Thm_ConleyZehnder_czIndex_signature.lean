-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_signature
-- name    : ConleyZehnder.czIndex_signature
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:23:02.442004+00:00
-- url     : https://prove2.me/theorems/f3d0b4a1-65e1-4684-aab3-eaae3433d168
-- title:
--   Signature property of the Conley–Zehnder index
-- statement:
--   Let $S$ be a real symmetric nondegenerate $2n\times2n$ matrix all of whose eigenvalues have absolute value $<2\pi$, and let $\psi(t)=\exp(tJ_0S)$, $t\in[0,1]$. Then
--   $$\mu_{CZ}(\psi)=\tfrac12\,\mathrm{Sign}(S),$$
--   where $\mathrm{Sign}(S)$ is the number of positive minus the number of negative eigenvalues of $S$.
--
--   **Formalization Note** Stated as $2\mu_{CZ}(\psi)=\mathrm{Sign}(S)$.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Proposition 8 (6), p. 7; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Gutt, Proposition 8 (6), Signature: for symmetric nondegenerate `S` with all
eigenvalues of absolute value `< 2π`, `μ_CZ(t ↦ exp(J₀ S t)) = ½ Sign(S)`. -/
theorem czIndex_signature (n : ℕ) : SignatureAxiom (czIndex (n := n)) := by sorry

end ConleyZehnder
