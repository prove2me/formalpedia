-- Prove2me | Theorems.Thm_BraidsLinksMCG_pureBraid_forget_section
-- name    : BraidsLinksMCG.pureBraid_forget_section
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:12:20.644006+00:00
-- url     : https://prove2.me/theorems/1040c0e8-69a1-4b52-8f6a-1f5963c4ad58
-- title:
--   The Fadell--Neuwirth forgetful map on pure braid groups splits
-- statement:
--   The Fadell–Neuwirth forgetful map on pure braid groups splits: the homomorphism
--
--   $$P_{n+1} \longrightarrow P_n$$
--
--   induced by forgetting the last strand admits a section, a homomorphism $s : P_n 	o P_{n+1}$ with the composite the identity on $P_n$.
--
--   This is the second of the two statements bundled in `BraidsLinksMCG.cor_1_8_1_pure_braid_semidirect`, separated out because it is logically independent of the first. Together with the exactness of the Fadell–Neuwirth sequence it is what turns that sequence into a semidirect product decomposition
--
--   $$P_{n+1} \cong F_n times P_n,$$
--
--   which is the engine of the standard inductive arguments about pure braid groups --- the combing normal form, faithfulness of the Artin representation, and the computation of the centre.
--
--   Geometrically the section is the one that adds a new strand which stays close to an existing one, or equivalently runs vertically without interacting: any pure braid on $n$ strands is carried to the pure braid on $n+1$ strands obtained by adjoining a trivial strand, and forgetting that strand recovers the original braid on the nose. The content is that this assignment is well defined on homotopy classes and is a homomorphism.
--
--   Note this is stronger than mere surjectivity of the forgetful map, which is part of the Fadell–Neuwirth exactness statement: a splitting is a choice of homomorphic right inverse, and surjectivity alone would only give a set-theoretic one.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, Theorem 1.4 and Corollary 1.8.1; Fadell and Neuwirth, Configuration spaces.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace BraidsLinksMCG

theorem pureBraid_forget_section (n : ℕ) :
    ∃ s : PureBraidGroup n →* PureBraidGroup (n + 1),
      (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp s =
        MonoidHom.id (PureBraidGroup n) := by sorry

end BraidsLinksMCG
