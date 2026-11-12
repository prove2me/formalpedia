-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_lemma_4_1
-- name    : EntropyLocalCoord.Leader.lemma_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:20:34.604092+00:00
-- url     : https://prove2.me/theorems/8e4fbb1a-0c61-4562-babc-810aa95ed9e8
-- title:
--   Lemma 4.1 — $\|df_X-df_Y\|_{TV}\le h(P(X\ne Y))$
-- statement:
--   Let $Z_1,\dots,Z_k$ be random variables on a probability space and let $X,Y$ be unbiased sign random variables, that is with values in $\{+1,-1\}$ and $P(X=1)=P(Y=1)=\tfrac12$, measurable with respect to $Z_1,\dots,Z_k$. With $p=P(X\ne Y)$,
--
--   $$\|df_X-df_Y\|_{TV}\le h(p),$$
--
--   where $df_X$ and $df_Y$ are the increments of the information CDFs in the fixed order of the sources and $h$ is the binary entropy function in bits.
--
--   This is the estimate that replaces a square-root loss by an entropy loss in the paper's main theorem.
--
--   Differences from the source:
--   - generalization: in §4 the variables $Z_1,\dots,Z_k$ are the mutually independent sources of a binary coordination profile → no independence hypothesis on the $Z_j$; the sources only need to be measurable; reason: the printed statement does not use independence, and the source's case is the special case of independent sources
--   - encoding: sources numbered $1,\dots,k$ with $df_X(\{j\})=f_X(j)-f_X(j-1)$ → index $j$ of `Fin k` carries $f_X(j+1)-f_X(j)$; reason: the same fixed ordering of $K$, shifted by one
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272, Lemma 4.1, p. 11.

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Information

open MeasureTheory

namespace EntropyLocalCoord.Leader

/-- Lemma 4.1, p. 11: for unbiased signs `X, Y` measurable with respect to `Z_1, …, Z_k` and
`p = P(X ≠ Y)`, one has `‖df_X - df_Y‖_TV ≤ h(p)`. -/
theorem lemma_4_1 {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {α : Fin k → Type*}
    [∀ l, MeasurableSpace (α l)] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ∀ l, Ω → α l) (hZ : ∀ l, Measurable (Z l)) (X Y : Ω → ℝ)
    (hXm : Measurable[sourceSigma Z Finset.univ] X)
    (hYm : Measurable[sourceSigma Z Finset.univ] Y)
    (hX : IsUnbiasedSign P X) (hY : IsUnbiasedSign P Y) :
    tvNorm (fun j => infoMeasure P Z X j - infoMeasure P Z Y j) ≤
      h (P.real {ω | X ω ≠ Y ω}) := by sorry

end EntropyLocalCoord.Leader
