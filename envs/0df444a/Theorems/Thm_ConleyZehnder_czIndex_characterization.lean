-- Prove2me | Theorems.Thm_ConleyZehnder_czIndex_characterization
-- name    : ConleyZehnder.czIndex_characterization
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T13:24:16.163778+00:00
-- url     : https://prove2.me/theorems/7a07ad4b-aac7-499f-9bca-41de6f380cd0
-- title:
--   Axiomatic characterization of the Conley–Zehnder index
-- statement:
--   For every $n\ge0$, the Conley–Zehnder index $\mu_{CZ}:\mathrm{SP}(n)\to\mathbb{Z}$, $\mu_{CZ}(\psi)=\deg(\hat\rho^2\circ\tilde\psi)$,
--
--   1. is constant on the connected components of $\mathrm{SP}(n)$ (**homotopy**);
--   2. satisfies $\mu_{CZ}(\varphi\psi)=\mu_{CZ}(\psi)+2\mu(\varphi)$ for every continuous loop $\varphi$ in $\mathrm{Sp}(2n)$ at $\mathrm{Id}$, with $\mu(\varphi)$ its Maslov index (**loop**);
--   3. satisfies $\mu_{CZ}(t\mapsto\exp(tJ_0S))=\tfrac12\mathrm{Sign}(S)$ for every symmetric nondegenerate $S$ with all eigenvalues of absolute value $<2\pi$ (**signature**);
--
--   and every map $\mu:\mathrm{SP}(n)\to\mathbb{Z}$ with these three properties equals $\mu_{CZ}$.
--
--   The index is thus the unique integer invariant of nondegenerate symplectic paths with these properties.
-- source:
--   Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse Math. 23 (2014) 907-932, https://doi.org/10.5802/afst.1430 (arXiv:1307.7239), Propositions 8 (2), (5), (6) and 9, pp. 6–7; Salamon, Lectures on Floer homology, IAS/Park City Math. Ser. 7 (1999) 143-229, https://doi.org/10.1090/pcms/007/05

import Definitions.Def_ConleyZehnder_Setting

namespace ConleyZehnder

/-- Salamon–Zehnder; Salamon (1999); Gutt, Propositions 8 and 9: the Conley–Zehnder index
`μ_CZ : SP(n) → ℤ` has the homotopy, loop and signature properties, and it is the only
map `SP(n) → ℤ` that has them. -/
theorem czIndex_characterization (n : ℕ) :
    (HomotopyAxiom (czIndex (n := n)) ∧ LoopAxiom (czIndex (n := n)) ∧
      SignatureAxiom (czIndex (n := n))) ∧
    ∀ μ : C(unitInterval, Mat n) → ℤ, HomotopyAxiom μ → LoopAxiom μ → SignatureAxiom μ →
      ∀ ψ ∈ SP n, μ ψ = czIndex ψ := by sorry

end ConleyZehnder
