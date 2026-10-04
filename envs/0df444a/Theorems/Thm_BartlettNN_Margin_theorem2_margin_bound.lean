-- Prove2me | Theorems.Thm_BartlettNN_Margin_theorem2_margin_bound
-- name    : BartlettNN.Margin.theorem2_margin_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:06:29.286007+00:00
-- url     : https://prove2.me/theorems/967fb5f4-e327-4b6f-8363-2845c21f03e9
-- title:
--   Theorem 2 — er_P(h) < êr^γ_z(h) + √((2/m)(d ln(34em/d) log₂(578m) + ln(4/δ))), d = fat_H(γ/16)
-- statement:
--   Let $X$ be a set, $H$ a class of real functions on $X$, $P$ a probability distribution on $X\times\{-1,1\}$, $0<\delta<1/2$ and $0<\gamma<1$. Suppose $z=((x_1,y_1),\dots,(x_m,y_m))$, $m\ge1$, is chosen by $m$ independent draws from $P$, and let $d=\operatorname{fat}_H(\gamma/16)$ be finite with $d\le 34m$. Then with probability at least $1-\delta$, every $h\in H$ has
--   $$
--   \operatorname{er}_P(h)\ <\ \widehat{\operatorname{er}}{}^{\gamma}_z(h)+\sqrt{\frac2m\Bigl(d\ln\frac{34em}{d}\,\log_2(578m)+\ln\frac4\delta\Bigr)} .
--   $$
--   Here $\operatorname{er}_P(h)=P\{\operatorname{sgn}(h(x))\ne y\}$ is the misclassification probability and $\widehat{\operatorname{er}}{}^{\gamma}_z(h)$ the fraction of training examples with $y_ih(x_i)<\gamma$.
--
--   This is the paper's margin bound: the accuracy of the margin error estimate depends on the fat-shattering dimension of $H$ at scale $\gamma/16$, not on the VC dimension or the number of parameters of the class.
--
--   **Formalization Note** *Correction.* The restriction $d\le 34m$ is added. The printed bound is not meaningful for every $d$: $d\ln(34em/d)$ decreases for $d>34m$, vanishes at $d=34em$ and is negative beyond, and near $d=34em$ the statement is false for rich classes (Lean's square root of a negative number is $0$). The proof covers $d\le 2m$, and for $2m<d\le 34m$ the right-hand side exceeds $1\ge\operatorname{er}_P(h)$, which is the paper's "the result is trivial otherwise"; on $[0,34m]$ the bound is increasing in $d$. $d=0$ is allowed and reads $d\ln(34em/d)=0$. "With probability at least $1-\delta$, every $h$ …" is a bound on the $P^m$-measure of the set of samples on which some $h\in H$ violates the inequality. The paper assumes all sets considered are measurable (p. 526); this is made explicit as the same three hypotheses as in Lemma 4: measurable hypotheses, measurable bad events $\{z:\exists h\in H,\ \operatorname{er}_P(h)\ge\widehat{\operatorname{er}}{}^{\gamma}_z(h)+\epsilon\}$, and measurable double-sample events of display (1). The standing assumptions $0<\delta<1/2$, $0<\gamma<1$ (p. 527) are explicit hypotheses; $e=\exp(1)$, $\ln$ is the natural logarithm.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 527, Theorem 2 (standing assumptions p. 527, measurability convention p. 526)

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

open MeasureTheory

namespace BartlettNN.Margin

/-- **Theorem 2** (Bartlett 1998, p. 527). Under the standing assumptions `0 < δ < 1/2` and
`0 < γ < 1`, for a sample `z` of `m ≥ 1` independent draws from `P`, with probability at least
`1 − δ` every `h ∈ H` has
`er_P(h) < êr^γ_z(h) + √((2/m)(d ln(34em/d) log₂(578m) + ln(4/δ)))`, where `d = fat_H(γ/16)`.
Correction: the statement is made for `d ≤ 34m`; beyond that the printed bound is not
meaningful (see the natural-language statement). The measurability hypotheses are the paper's
standing assumption (p. 526), as in Lemma 4. -/
theorem theorem2_margin_bound {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (H : Set (X → ℝ))
    (γ δ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2)
    (m d : ℕ) (hm : 1 ≤ m) (hd : fat H (γ / 16) = d) (hd34 : d ≤ 34 * m)
    (hHmeas : ∀ h ∈ H, Measurable h)
    (hbad : ∀ ε : ℝ, MeasurableSet {z : Fin m → X × Bool | ∃ h ∈ H, erHat γ z h + ε ≤ er P h})
    (hghost : ∀ ε : ℝ, MeasurableSet {w : Fin (m + m) → X × Bool | ∃ h ∈ H,
      ((Finset.univ.filter fun i : Fin m =>
          γ ≤ |squash γ (h (w (Fin.natAdd m i)).1) - γ * pm (w (Fin.natAdd m i)).2|).card : ℝ) / m
        ≥ ((Finset.univ.filter fun i : Fin m =>
          squash γ (h (w (Fin.castAdd m i)).1) ≠ γ * pm (w (Fin.castAdd m i)).2).card : ℝ) / m
          + ε / 2}) :
    Measure.pi (fun _ : Fin m => P)
      {z | ∃ h ∈ H, erHat γ z h + Real.sqrt ((2 / m) *
          (d * Real.log (34 * Real.exp 1 * m / d) * Real.logb 2 (578 * m) + Real.log (4 / δ)))
        ≤ er P h}
      ≤ ENNReal.ofReal δ := by sorry

end BartlettNN.Margin
