-- Prove2me | Theorems.Thm_DiazModulus_logAlg_conj_stable
-- name    : DiazModulus.logAlg_conj_stable
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T06:43:41.160434+00:00
-- url     : https://prove2.me/theorems/95246d4a-a61c-4120-bfd0-0f30ffec3055
-- title:
--   $\mathcal{L}$ is stable under complex conjugation
-- statement:
--   If $u$ is a logarithm of an algebraic number, so is $\bar u$.
--
--   Concretely: if $e^{u}$ is algebraic then $e^{\bar u}$ is algebraic, because $e^{\bar u} = \overline{e^{u}}$ and a polynomial with rational coefficients that annihilates $z$ also annihilates $\bar z$ (its coefficients are fixed by conjugation).
--
--   This is elementary, but it is the first thing every later argument in the mission uses. A hypothetical counterexample $u$ to Diaz's question has $\bar u \in \mathcal{L}$ as well, and that is exactly what puts the pair $(u,\bar u)$ inside the reach of Schanuel's conjecture and of the four-exponentials configuration.
-- source:
--   G. Diaz, Utilisation de la conjugaison complexe dans l'etude de la transcendance de valeurs de la fonction exponentielle usuelle, J. Theor. Nombres Bordeaux 16 (2004), no. 3, 535-553, doi:10.5802/jtnb.459, section 5.1, p. 550

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem logAlg_conj_stable (u : ℂ) (h : u ∈ LogAlg) : conj u ∈ LogAlg := by sorry
end DiazModulus
