-- Prove2me | Theorems.Thm_DetDLP_s8g_fp_moment_wired_encoders
-- name    : DetDLP.s8g_fp_moment_wired_encoders
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-24T19:18:35.265844+00:00
-- url     : https://prove2.me/theorems/b65fadd9-f070-40e7-9dae-3b90eef00e67
-- title:
--   Wired Uniform address compilers for F_p Stage I moment queries
-- statement:
--   There exists a single uniform polynomial-time address compiler, constructed from the Stage I arithmetic gadget laws and a modular-multiplication interface, that simultaneously realizes every multiplicative moment query of Theorem 3.1.
--
--   $$
--   \exists\,a:\mathrm{Addresses}.\ a\text{ is Uniform and }\forall p,j,T,\eta:\ \mathrm{Realizes}(\mathrm{make}(a),\mathrm{port}(a),200000; w_{p,j,T,\eta}).
--   $$
--
--   This replaces the unsound split into an arbitrary Uniform address map plus a layout obligation for every such map.
-- source:
--   Liu–Zhang–Ren Formal Paper, Theorem 3.1

import Definitions.Def_DetDLP_S8G_FpMomentGraph
import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_W3_ModMul

set_option autoImplicit false

namespace DetDLP

open S8C
open S8G.FpMoment
open S8G.FpMoment.Code
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/--
Correct packaging of Stage I tag-1 encoders: a *single* uniform address compiler
together with the realization obligations for every moment query.

(The earlier split `s8g_fp_moment_addresses` + `s8g_fp_moment_layout_realizes` is
unsound as a reduction because an arbitrary `Uniform` address map need not wire the
moment layouts; only a compiler constructed from the gadget laws does.)
-/
theorem s8g_fp_moment_wired_encoders (h : S8C.GadgetLaws) (mul : w3_modMulInterface) :
    ∃ a : Addresses,
      a.Uniform ∧
        ∀ (p : ℕ) [Fact p.Prime] (j : Fin 4) (T : ℕ) (η : List Bool),
          T ≤ p → η.length ≤ blockCount (bitLen p) * 2 * bitLen p →
          S8C.Realizes (make a) (port a) 200000 (word p j T η) (bitLen p)
            (value p (blockCount (bitLen p)) T η j) := by sorry

end DetDLP
