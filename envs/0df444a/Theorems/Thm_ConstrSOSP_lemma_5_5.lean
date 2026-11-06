-- Prove2me | Theorems.Thm_ConstrSOSP_lemma_5_5
-- name    : ConstrSOSP.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:07:30.741132+00:00
-- url     : https://prove2.me/theorems/298851fb-0653-4ac7-95c5-ae5ccc5a89ed
-- title:
--   Lemma 5.5: $f$, $\nabla f$, $\nabla^2f$ are computable in polynomial time
-- statement:
--   **Theorem.** There are three polynomial-time computable maps which, given a well-formed Iter circuit $C$ and rationals $x,y\in[0,N]$ (in binary), output the rational value $f(x,y)$, the rational gradient $\nabla f(x,y)$ and the rational Hessian $\nabla^2f(x,y)$ of the constructed function, in binary.
--
--   The running time is polynomial in the bit lengths of $x$, $y$ and the size of $C$, although the grid has exponentially many cells: only the corner data of the cell containing $(x,y)$ are needed.
--
--   Differences from the source:
--   - encoding: Turing machines C_f, C_∇f, C_∇²f with input x, y and the circuit C → polynomial-time computable maps (Cook Turing machines) on the input encCircuit C ++ encRat x ++ encRat y, with outputs encRat, encRatVec 2, encRatMatrix 2; reason: Lean convention; same computations
--   - encoding: ∇f, ∇²f of the C² function → Mathlib Fréchet derivatives (gradVec, hessMat); vector norms written out as Euclidean norms; reason: Lean convention; same values for C² functions
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Lemma 5.5, p.52 (proof pp.52–53)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_ConstrSOSP_Circuit_WF
import Definitions.Def_ConstrSOSP_encCircuit
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_fGrid
import Definitions.Def_ConstrSOSP_gradVec
import Definitions.Def_ConstrSOSP_hessMat

namespace ConstrSOSP

open QAlgorithms.LocalHamiltonian CardinalMatching

/-- **Lemma 5.5** (arXiv:2604.02285, 2 Nov 2026, p.52): "There exist polynomial-time Turing
machines C_f, C_∇f, C_∇²f such that given two numbers x, y ∈ [0, N] with bit complexity len(x)
and len(y) respectively we can compute the value, the gradient of f and the hessian of f at any
point in time that is polynomial in len(x), len(y) and in the size of the Boolean circuit C of
Iter."

There are three polynomial-time computable maps (Cook's Turing machines) that, on the input
`encCircuit C ++ encRat x ++ encRat y` for a well-formed circuit `C` and rationals
`x, y ∈ [0, N]`, output the binary codes of the rational value `f(x, y)`, gradient `∇f(x, y)`
and Hessian `∇²f(x, y)` of the constructed function `f = fGrid C`. -/
theorem lemma_5_5 :
    ∃ Φf Φg ΦH : List Bool → List Bool,
      CookPvsNP.PolyTimeComputable Φf ∧ CookPvsNP.PolyTimeComputable Φg ∧
      CookPvsNP.PolyTimeComputable ΦH ∧
      ∀ C : Circuit, C.WF → ∀ x y : ℚ, 0 ≤ x → x ≤ (gridN C.n : ℚ) → 0 ≤ y →
        y ≤ (gridN C.n : ℚ) →
        (∃ r : ℚ, Φf (encCircuit C ++ encRat x ++ encRat y) = encRat r ∧
          (r : ℝ) = fGrid C ![(x : ℝ), (y : ℝ)]) ∧
        (∃ g : Fin 2 → ℚ, Φg (encCircuit C ++ encRat x ++ encRat y) = encRatVec 2 g ∧
          ∀ i, (g i : ℝ) = gradVec (fGrid C) ![(x : ℝ), (y : ℝ)] i) ∧
        (∃ H : Fin 2 → Fin 2 → ℚ, ΦH (encCircuit C ++ encRat x ++ encRat y) = encRatMatrix 2 H ∧
          ∀ i j, (H i j : ℝ) = hessMat (fGrid C) ![(x : ℝ), (y : ℝ)] i j) := by sorry

end ConstrSOSP
