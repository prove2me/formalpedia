-- Prove2me | Theorems.Thm_DrezetGHZ_ghz_eigen_relations
-- name    : DrezetGHZ.ghz_eigen_relations
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-28T19:25:17.900224+00:00
-- url     : https://prove2.me/theorems/e7a6fed1-c25e-4799-b856-82fdb78fd98a
-- title:
--   Eqs. (2)–(5): the GHZ state is an eigenvector of $\sigma_x\sigma_x\sigma_x$ and of the $\sigma_x\sigma_y\sigma_y$-type operators
-- statement:
--   Let $|\psi\rangle=\frac1{\sqrt2}(|{+z}{+z}{+z}\rangle-|{-z}{-z}{-z}\rangle)$ be the GHZ state. Then
--   $$\sigma_x^{(1)}\sigma_x^{(2)}\sigma_x^{(3)}|\psi\rangle=-|\psi\rangle,\qquad \sigma_x^{(1)}\sigma_y^{(2)}\sigma_y^{(3)}|\psi\rangle=|\psi\rangle,$$
--   $$\sigma_y^{(1)}\sigma_x^{(2)}\sigma_y^{(3)}|\psi\rangle=|\psi\rangle,\qquad \sigma_y^{(1)}\sigma_y^{(2)}\sigma_x^{(3)}|\psi\rangle=|\psi\rangle.$$
--
--   These four eigenvalue relations are the perfect correlations on which the GHZ argument rests.
-- source:
--   A. Drezet, "An Elementary Proof That Everett's Quantum Multiverse Is Nonlocal: Bell-Locality and Branch-Symmetry in the Many-Worlds Interpretation", arXiv:2306.07794v1 [quant-ph] (2023), https://arxiv.org/abs/2306.07794, p. 3, Eqs. (2)–(5).

import Mathlib
import Definitions.Def_DrezetGHZ_Quantum
open Matrix

namespace DrezetGHZ
theorem ghz_eigen_relations :
    tensor3 pauliX pauliX pauliX *ᵥ ghzState = -ghzState ∧
    tensor3 pauliX pauliY pauliY *ᵥ ghzState = ghzState ∧
    tensor3 pauliY pauliX pauliY *ᵥ ghzState = ghzState ∧
    tensor3 pauliY pauliY pauliX *ᵥ ghzState = ghzState := by sorry
end DrezetGHZ
