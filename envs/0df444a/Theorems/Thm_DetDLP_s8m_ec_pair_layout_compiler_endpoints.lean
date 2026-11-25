-- Prove2me | Theorems.Thm_DetDLP_s8m_ec_pair_layout_compiler_endpoints
-- name    : DetDLP.s8m_ec_pair_layout_compiler_endpoints
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-25T05:37:54.068954+00:00
-- url     : https://prove2.me/theorems/0b9c76b5-5885-5f26-8c1f-e29c2e877163
-- title:
--   Tag-6 pair compiler endpoint witness
-- statement:
--   From the gadget laws, there exist total polynomial-time address fields $(n_V,n_E,\mathrm{src},\mathrm{dst},\mathrm{check})$ such that every tag-6 elliptic pair query is wired to some factor layout $A$. The satisfying assignments of $A$ are in bijection with a finite set whose cardinality equals the pair count, the layout meets the Stage-I edge and degree budgets, and the fields reproduce the vertex count, edge count, endpoints, and subdivision tensor of $A$. Packaging these fields as an `Addresses` record and applying the proved packet lemmas `make_word` and `port_word` yields the uniform compiler witness. The fields are not an arbitrary uniform address record: a counterexample address can be uniform and still fail to encode $A$.
-- source:
--   DetDLP Stage I, tag-6 pair layout compiler; reduction of s8m_ec_pair_layout_compiler_witness

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8M_ECPairPacket
import Definitions.Def_DetDLP_S8C_TagSpec

set_option autoImplicit false

namespace DetDLP

open S8C
open S8M.ECPair
open S8M.ECPair.Packet
open Groundwork
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/--
Endpoint form of the tag-6 compiler: polynomial address fields, not an arbitrary
uniform record, whose `nv`/`ne`/`src`/`dst`/`check` match a factor layout that
already carries the witness count and the Stage-I budgets. `Packet.make_word`
and `Packet.port_word` turn those equations into the BTN packet.
-/
theorem s8m_ec_pair_layout_compiler_endpoints (h : S8C.GadgetLaws) :
    ∃ (nv ne : List Bool → ℕ) (src dst : List Bool → ℕ → ℕ)
      (check : List Bool × ℕ × List Bool → Bool),
      PolyT nv ∧ PolyT ne ∧
        Unary (fun w => nv w + ne w) ∧
        Unary (fun w => ne w + ne w) ∧
        PolyT (fun z : List Bool × ℕ => src z.1 z.2) ∧
        PolyT (fun z : List Bool × ℕ => dst z.1 z.2) ∧
        PolyT check ∧
        ∀ (p : ℕ) [Fact p.Prime], 3 < p →
          ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
            ∀ (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool),
              T ≤ p → η.length ≤ 2 * blockCount (bitLen p) * (2 * bitLen p + 1) →
              ∃ (A : w3_FactorLayout) (test : w3_factorTest A) (hg : Function.Surjective A.gate)
                (W : Type) (instW : Fintype W)
                (witness :
                  {b : Fin A.nb → Bool // ∀ g, test g (fun e => b (A.bit e.1)) = true} ≃ W),
                Fintype.card W = value E T S X η ∧
                  2 * A.ne < scale (blockCount (bitLen p)) (bitLen p) ∧
                  (∀ v, (w3_factorGraph A).deg v ≤
                    max 12 (Nat.ceil (136 * ((bitLen p : ℝ) + 2) ^ ((3 : ℝ) / 4)))) ∧
                  nv (word E T S X η) = (w3_factorGraph A).nV ∧
                  ne (word E T S X η) = (w3_factorGraph A).nE ∧
                  (∀ i : Fin (w3_factorGraph A).nE,
                    src (word E T S X η) i.val = ((w3_factorGraph A).endpoints i).1.val) ∧
                  (∀ i : Fin (w3_factorGraph A).nE,
                    dst (word E T S X η) i.val = ((w3_factorGraph A).endpoints i).2.val) ∧
                  ∀ v a',
                    check (word E T S X η, v.val, List.ofFn a') =
                      (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a' := by
  sorry

end DetDLP
