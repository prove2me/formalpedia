-- Prove2me | Theorems.Thm_BartlettNN_Margin_lemma4_covering_margin_bound
-- name    : BartlettNN.Margin.lemma4_covering_margin_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:05:59.648526+00:00
-- url     : https://prove2.me/theorems/02146583-8c0a-42ed-8a9f-1aa6c4afda64
-- title:
--   Lemma 4 — er_P(h) < êr^γ_z(h) + √((2/m) ln(2N∞(π_γ(H), γ/2, 2m)/δ))
-- statement:
--   Let $X$ be a set, $H$ a class of real functions on $X$, $P$ a probability distribution on $X\times\{-1,1\}$, $\gamma>0$ and $0<\delta<1/2$. Let $z=((x_1,y_1),\dots,(x_m,y_m))$, $m\ge 1$, be chosen by $m$ independent draws from $P$. Then with probability at least $1-\delta$, every $h\in H$ has
--   $$
--   \operatorname{er}_P(h)<\widehat{\operatorname{er}}{}^{\gamma}_z(h)+\sqrt{\frac2m\ln\Bigl(\frac{2\,\mathcal N_\infty(\pi_\gamma(H),\gamma/2,2m)}{\delta}\Bigr)} .
--   $$
--   Here $\operatorname{er}_P$ is the misclassification probability, $\widehat{\operatorname{er}}{}^{\gamma}_z$ the margin error estimate, $\pi_\gamma(H)$ the squashed class and $\mathcal N_\infty$ the $\ell_\infty$ covering number on samples of length $2m$.
--
--   This is the first half of the proof of Theorem 2: it bounds the misclassification probability uniformly over $H$ by a covering number of the squashed class.
--
--   **Formalization Note** "With probability at least $1-\delta$, every $h$ has …" is stated as: the $m$-fold product of $P$ gives measure at most $\delta$ to the set of samples on which some $h\in H$ violates the bound. The bound is asserted for every natural number $N\ge\mathcal N_\infty(\pi_\gamma(H),\gamma/2,2m)$ in place of $\mathcal N_\infty$; when $\mathcal N_\infty=\infty$ the printed bound is $+\infty$ and says nothing. The paper ignores measurability and assumes all sets considered are measurable (p. 526: "Throughout, we ignore issues of measurability, and assume that all sets considered are measurable."); this is made explicit as three hypotheses: every $h\in H$ is measurable, the event "some $h\in H$ has $\operatorname{er}_P(h)\ge\widehat{\operatorname{er}}{}^{\gamma}_z(h)+\epsilon$" is measurable for every $\epsilon$, and the double-sample event of display (1) of the proof is measurable for every $\epsilon$ (the double sample $(z,\tilde z)$ is one sample of length $2m$ whose first $m$ entries are $z$). $m\ge 1$ is implicit in the factor $1/m$.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 527, Lemma 4

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_FatShattering
import Definitions.Def_BartlettNN_Margin_Squash
import Definitions.Def_BartlettNN_Margin_Covering

open MeasureTheory

namespace BartlettNN.Margin

/-- **Lemma 4** (Bartlett 1998, p. 527). For `γ > 0`, `0 < δ < 1/2` and a sample of `m ≥ 1`
independent draws from `P`, with probability at least `1 − δ` every `h ∈ H` has
`er_P(h) < êr^γ_z(h) + √((2/m) ln(2 N∞(π_γ(H), γ/2, 2m)/δ))`. The bound is stated for every
finite `N ≥ N∞(π_γ(H), γ/2, 2m)` (when `N∞ = ⊤` the printed bound is `+∞`). The measurability
hypotheses are the paper's standing assumption that all sets considered are measurable (p. 526):
the hypotheses, the bad events of the first display of the proof, and the double-sample events
of display (1) (first `m` coordinates are `z`, last `m` are `z̃`). -/
theorem lemma4_covering_margin_bound {X : Type*} [MeasurableSpace X]
    (P : Measure (X × Bool)) [IsProbabilityMeasure P] (H : Set (X → ℝ))
    (γ δ : ℝ) (hγ : 0 < γ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (m : ℕ) (hm : 1 ≤ m)
    (hHmeas : ∀ h ∈ H, Measurable h)
    (hbad : ∀ ε : ℝ, MeasurableSet {z : Fin m → X × Bool | ∃ h ∈ H, erHat γ z h + ε ≤ er P h})
    (hghost : ∀ ε : ℝ, MeasurableSet {w : Fin (m + m) → X × Bool | ∃ h ∈ H,
      ((Finset.univ.filter fun i : Fin m =>
          γ ≤ |squash γ (h (w (Fin.natAdd m i)).1) - γ * pm (w (Fin.natAdd m i)).2|).card : ℝ) / m
        ≥ ((Finset.univ.filter fun i : Fin m =>
          squash γ (h (w (Fin.castAdd m i)).1) ≠ γ * pm (w (Fin.castAdd m i)).2).card : ℝ) / m
          + ε / 2})
    (N : ℕ) (hN : Ninf (squashClass γ H) (γ / 2) (2 * m) ≤ N) :
    Measure.pi (fun _ : Fin m => P)
      {z | ∃ h ∈ H, erHat γ z h + Real.sqrt ((2 / m) * Real.log (2 * N / δ)) ≤ er P h}
      ≤ ENNReal.ofReal δ := by sorry

end BartlettNN.Margin
