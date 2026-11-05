-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Fact_sum_words_eq
-- name    : ClauseBound.Inst.Half.Fact.sum_words_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:51.973778+00:00
-- url     : https://prove2.me/theorems/dda147ba-fdb8-452c-8167-33d5ce4358a6
-- title:
--   Fact: sum words eq
-- statement:
--   The sum over all labels of the product of the two programs is the double sum over j and the
--   monomials of the weight that belongs to j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfFact.lean#L52-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfFact.lean#L52-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfFact
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Finset
open ClauseBound.Inst.Half.Fact

theorem ClauseBound.Inst.Half.Fact.sum_words_eq (hW : StWords) (hL : StLabs) (hV : StVal) {c₀ c lam : ℕ} {pad : U} (hl : 1 ≤ lam) (hC : Cst c₀ c lam)
    (hp : 2 ^ (c * lam) ≤ pad.length) (tr : Bool) (h' : ℕ) {i : ℕ} (hi : i < 4 * ClauseBound.Part.hOf lam + 1) (a b a' b' : Pieces.Bits lam) :
    ∑ θ ∈ words ((halfF c₀ c).cap tr h' lam i),
        (halfF c₀ c).top ((pad, tr), (h', i), (bitsOf a, bitsOf b, θ)) * (halfF c₀ c).bot ((pad, tr), (h', i), (bitsOf a', bitsOf b', θ))
      = ∑ j ∈ range (2 * ClauseBound.Part.hOf lam + 1), ∑ τ ∈ ClauseBound.Boson.Pz (wOf tr (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) j),
          (bif tr then ClauseBound.Boson.topK (ell (ClauseBound.Part.hOf lam) a) (ClauseBound.Part.hOf lam) j ((i : ℤ) - 2 * ClauseBound.Part.hOf lam - ClauseBound.Part.hOf lam + j)
              (ell (ClauseBound.Part.hOf lam) b : Multiset ℕ) τ
            else ClauseBound.Boson.topK (ell (ClauseBound.Part.hOf lam) a) (ClauseBound.Part.hOf lam) j ((i : ℤ) - 2 * ClauseBound.Part.hOf lam - ClauseBound.Part.hOf lam + j)
              τ (ell (ClauseBound.Part.hOf lam) b : Multiset ℕ)) *
          (bif tr then ClauseBound.Boson.botK (ell (ClauseBound.Part.hOf lam) b') (ClauseBound.Part.hOf lam) (ClauseBound.Part.hOf lam - ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) - j)
              τ (ell (ClauseBound.Part.hOf lam) a' : Multiset ℕ)
            else ClauseBound.Boson.botK (ell (ClauseBound.Part.hOf lam) b') (ClauseBound.Part.hOf lam) (ClauseBound.Part.hOf lam - ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) - j)
              (ell (ClauseBound.Part.hOf lam) a' : Multiset ℕ) τ) := by sorry
