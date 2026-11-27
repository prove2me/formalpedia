-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_A_2_4
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_A_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:10:33.090371+00:00
-- url     : https://prove2.me/theorems/3a26a92f-706d-596f-b9f4-cbe5d0cbdb54
-- title:
--   Theorem A.2.4 (corrected: upper semicontinuity in a) — measurable maximizer and measurable maximum on compact sections
-- statement:
--   Let $E$, $A$ be Borel spaces and $x \mapsto  D(x)$ a compact-valued mapping such that $D := \{(x, a) \in  E \times  A | a \in  D(x)\}$ is a Borel subset of $E \times  A$. Let $w : D \to  \mathbb R $ be Borel measurable **and let $a \mapsto  w(x, a)$ be upper semicontinuous on $D(x)$ for every $x \in  E$**. Then there exists a Borel measurable maximizer $f$ of $w$: a Borel measurable $f : E \to  A$ with $f(x) \in  D(x)$ for all $x \in  E$ and $w(x, f(x)) = \sup _{a \in  D(x)} w(x, a) =: v(x)$. Moreover, $v$ is Borel measurable.
--
--   **Formalization Note.** As printed (without the bold premise) the theorem is false: $E$ a point, $A = D = [0, 1]$, $w(a) = a$ for $a < 1$, $w(1) = 0$ is Borel and has no maximum point. The premise is the upper semicontinuity of Proposition 2.4.11, whose proof this theorem is, and holds in every use of the theorem in the book. Borel spaces are encoded as in the published Theorem A.2.3 (`MetrizableSpace`, `SecondCountableTopology`, `BorelSpace`, `StandardBorelSpace`); $D(x)$ is nonempty, as in the book's definition of a set-valued mapping (p.351). $w$ is given on $E \times  A$; only its values on $D$ enter, and a Borel function on the Borel set $D$ extends by $0$ to a Borel function on $E \times  A$. The maximum property is $\forall  a \in  D(x), w(x, a) \le  w(x, f(x))$; $v$ is the supremum over the subtype $D(x)$, which is attained, so no junk value of a real supremum enters.
--
--   Differences from the source:
--   - correction: w Borel measurable → w Borel measurable and a ↦ w(x,a) upper semicontinuous on D(x); reason: false as printed: E a point, A = D = [0,1], w(a) = a for a < 1, w(1) = 0 has no maximum point
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem A.2.4, p.352 (PDF 358)

import Mathlib

open MeasureTheory

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem A.2.4** (corrected) (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), Theorem A.2.4, p.352, PDF 358). Let `E`, `A` be Borel spaces and `x ↦ D(x)` a
compact-valued mapping such that `D := {(x, a) ∈ E × A | a ∈ D(x)}` is a Borel subset of `E × A`.
Let `w : D → ℝ` be Borel measurable **and let `a ↦ w(x, a)` be upper semicontinuous on `D(x)` for
every `x ∈ E`**. Then there exists a Borel measurable maximizer `f` of `w`: a Borel measurable
`f : E → A` with `f(x) ∈ D(x)` for all `x ∈ E` and `w(x, f(x)) = sup_{a ∈ D(x)} w(x, a) =: v(x)`.
Moreover, `v` is Borel measurable.

**Formalization Note.** As printed (without the bold premise) the theorem is false: `E` a point,
`A = D = [0, 1]`, `w(a) = a` for `a < 1`, `w(1) = 0` is Borel and has no maximum point. The premise
is the upper semicontinuity of Proposition 2.4.11, whose proof this theorem is, and holds in every
use of the theorem in the book. Borel spaces are encoded as in the published Theorem A.2.3
(`MetrizableSpace`, `SecondCountableTopology`, `BorelSpace`, `StandardBorelSpace`); `D(x)` is
nonempty, as in the book's definition of a set-valued mapping (p.351). `w` is given on `E × A`;
only its values on `D` enter, and a Borel function on the Borel set `D` extends by `0` to a Borel
function on `E × A`. The maximum property is `∀ a ∈ D(x), w(x, a) ≤ w(x, f(x))`; `v` is the
supremum over the subtype `D(x)`, which is attained, so no junk value of a real supremum enters. -/
theorem theorem_A_2_4 {E A : Type*}
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace E]
    [TopologicalSpace A] [TopologicalSpace.MetrizableSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] [StandardBorelSpace A]
    (D : E → Set A) (hD_ne : ∀ x, (D x).Nonempty) (hD_cpt : ∀ x, IsCompact (D x))
    (hD_graph : MeasurableSet {p : E × A | p.2 ∈ D p.1})
    (w : E × A → ℝ) (hw : Measurable w)
    (hw_usc : ∀ x, UpperSemicontinuousOn (fun a => w (x, a)) (D x)) :
    ∃ f : E → A, Measurable f ∧ (∀ x, f x ∈ D x) ∧
      (∀ x, ∀ a ∈ D x, w (x, a) ≤ w (x, f x)) ∧
      (∀ x, w (x, f x) = ⨆ a : D x, w (x, (a : A))) ∧
      Measurable (fun x => ⨆ a : D x, w (x, (a : A))) := by sorry

end BauerleRiederMDP.LQ.Supplement
