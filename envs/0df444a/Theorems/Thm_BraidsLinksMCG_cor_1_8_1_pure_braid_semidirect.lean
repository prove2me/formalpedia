-- Prove2me | Theorems.Thm_BraidsLinksMCG_cor_1_8_1_pure_braid_semidirect
-- name    : BraidsLinksMCG.cor_1_8_1_pure_braid_semidirect
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T18:59:48.424294+00:00
-- url     : https://prove2.me/theorems/6c5a58a8-e969-4220-a437-d9a44dc405b7
-- title:
--   Corollary 1.8.1: $P_n$ is a semidirect product of a free group and $P_{n-1}$
-- statement:
--   **Corollary 1.8.1 (indexed as $P_{n+1} = U_{n+1} \rtimes P_n$).** The pure braid group
--   $P_{n+1} = \pi_1 F_{0,n+1}E^2$ is a semidirect product of the free group $U_{n+1}$ of rank $n$ by
--   $P_n$. Combined with Theorem 1.4, which identifies $U_{n+1}$ with the kernel of
--   $\pi_* : P_{n+1} \to P_n$ and with $\pi_1$ of the plane punctured at $n$ points, the statement
--   formalized here has two parts:
--
--   1. the fundamental group of $E^2 - \{1, \dots, n\}$ is free of rank $n$;
--   2. the surjection $\pi_* : P_{n+1} \to P_n$ induced by deleting the last point admits a
--      homomorphic section, i.e. a homomorphism $s : P_n \to P_{n+1}$ with $\pi_* \circ s = \mathrm{id}$.
--
--   An exact sequence with free kernel and a section exhibits the middle group as a semidirect
--   product, which is the assertion of the corollary.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, p. 24, Corollary 1.8.1 (with $U_n$ the free subgroup of rank $n-1$ from the proof of Theorem 1.8, pp. 19–23); indexed here as $P_{n+1} = U_{n+1} \rtimes P_n$

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem cor_1_8_1_pure_braid_semidirect (n : ℕ) :
    Nonempty (PuncturedPlaneGroup n ≃* FreeGroup (Fin n)) ∧
      ∃ s : PureBraidGroup n →* PureBraidGroup (n + 1),
        (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp s =
          MonoidHom.id (PureBraidGroup n) := by sorry

end BraidsLinksMCG
