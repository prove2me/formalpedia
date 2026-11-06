-- Prove2me | Theorems.Thm_ConstrSOSP_frame_polytime
-- name    : ConstrSOSP.frame_polytime
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:09:45.375517+00:00
-- url     : https://prove2.me/theorems/7ead9cab-e88e-45fb-9560-b66e29471229
-- title:
--   $F$, $\nabla F$, $\nabla^2F$ are computable in polynomial time
-- statement:
--   **Theorem.** There are three polynomial-time computable maps which, given a well-formed Iter circuit $C$ and rationals $x,y\in[0,1]$ (in binary), output the rational value, gradient and Hessian of the normalized function $F$ at $(x,y)$, in binary.
--
--   This is the analogue of Lemma 5.5 for the framed and normalized function, and it provides the Turing machines of the final instance.
--
--   Differences from the source:
--   - encoding: polynomial-time computability of the interpolants ("by the same argument as Lemma 5.5") → polynomial-time computable maps (Cook Turing machines) on encCircuit C ++ encRat x ++ encRat y, with outputs encRat, encRatVec 2, encRatMatrix 2; reason: Lean convention; same computations
--   - encoding: ∇f, ∇²f of the C² function → Mathlib Fréchet derivatives (gradVec, hessMat); vector norms written out as Euclidean norms; reason: Lean convention; same values for C² functions
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), proof of Corollary 5.6, p.56

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_encCircuit
import Definitions.Def_ConstrSOSP_Fnorm
import Definitions.Def_ConstrSOSP_gradVec
import Definitions.Def_ConstrSOSP_hessMat

namespace ConstrSOSP

open QAlgorithms.LocalHamiltonian CardinalMatching

/-- **`F`, `∇F`, `∇²F` are polynomial-time evaluable** (arXiv:2604.02285, 2 Nov 2026, proof of
Corollary 5.6, p.56: "The extra corner data and their interpolants are computable in polynomial
time by the same argument as Lemma 5.5.").

There are three polynomial-time computable maps (Cook's Turing machines) that, on the input
`encCircuit C ++ encRat x ++ encRat y` for a well-formed circuit `C` and rationals
`x, y ∈ [0, 1]`, output the binary codes of the rational value, gradient and Hessian of the
normalized function `F = Fnorm C` at `(x, y)`. -/
theorem frame_polytime :
    ∃ Φf Φg ΦH : List Bool → List Bool,
      CookPvsNP.PolyTimeComputable Φf ∧ CookPvsNP.PolyTimeComputable Φg ∧
      CookPvsNP.PolyTimeComputable ΦH ∧
      ∀ C : Circuit, C.WF → ∀ x y : ℚ, 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
        (∃ r : ℚ, Φf (encCircuit C ++ encRat x ++ encRat y) = encRat r ∧
          (r : ℝ) = Fnorm C ![(x : ℝ), (y : ℝ)]) ∧
        (∃ g : Fin 2 → ℚ, Φg (encCircuit C ++ encRat x ++ encRat y) = encRatVec 2 g ∧
          ∀ i, (g i : ℝ) = gradVec (Fnorm C) ![(x : ℝ), (y : ℝ)] i) ∧
        (∃ H : Fin 2 → Fin 2 → ℚ, ΦH (encCircuit C ++ encRat x ++ encRat y) = encRatMatrix 2 H ∧
          ∀ i j, (H i j : ℝ) = hessMat (Fnorm C) ![(x : ℝ), (y : ℝ)] i j) := by sorry

end ConstrSOSP
