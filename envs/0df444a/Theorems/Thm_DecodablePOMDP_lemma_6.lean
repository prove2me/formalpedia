-- Prove2me | Theorems.Thm_DecodablePOMDP_lemma_6
-- name    : DecodablePOMDP.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:39.359492+00:00
-- url     : https://prove2.me/theorems/f9ef6edf-ab3f-4240-a2f0-643f0bae712b
-- title:
--   Lemma 6 — a simplex grid with $\ell_1$ rounding error $\eta$ and at most $(4e/\eta)^d$ points
-- statement:
--   Let $d\ge1$ be the number of coordinates and $0<\eta\le1$. The lattice grid $G_{d,\eta}$ of App. A.6 satisfies:
--
--   1. $G_{d,\eta}\subset\Delta_d$;
--   2. for every $w\in\Delta_d$ there is $g\in G_{d,\eta}$ with $\|w-g\|_1\le\eta$;
--   3. $|G_{d,\eta}|\le(C/\eta)^d$ with $C=4e$;
--   4. (face version) for every coordinate set $\mathcal A$, every $q^*\in\mathcal A$ and every $w\in\Delta_d$ supported on $\mathcal A$, the face rounding $g$ of $w$ (remaining mass at $q^*$) lies in $G_{d,\eta}$, vanishes outside $\mathcal A$, and $\|w-g\|_1\le\eta$.
--
--   The planner rounds its weights with clause 4, so its state space is finite with the stated size.
--
--   Differences from the source:
--   - generalization: "there is a finite grid G_{d,η} … for some universal constant C" → the explicit lattice grid of A.6 with C = 4e; reason: explicit grid and constant imply the existential statement
--   - generalization: the statement of Lemma 6 → plus the face-rounding claim of A.6, p.17, for every choice of the coordinate q*; reason: printed in the proof of Lemma 6 and used by the planner ("Rounding is performed within G_h(u), with the same accuracy and size bounds as in Lemma 6", p.10)
--   - generalization: Δ_d ⊂ ℝ^d → probability vectors on any nonempty finite index type ι, d = |ι|; reason: ι = Fin d is ℝ^d; the planner uses ι = Q
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Lemma 6, p.10 (proof A.6, p.17)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_DecodablePOMDP_Grid

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **Lemma 6 — a simplex grid with ℓ₁ rounding error η and at most `(C/η)^d` points.** Let
`d ≥ 1` (here `d = |ι|` coordinates) and `0 < η ≤ 1`. The lattice grid `G_{d,η}` of A.6
1. lies in the probability simplex `Δ_d`;
2. contains, for every `w ∈ Δ_d`, a rounding point `g` with `‖w − g‖₁ ≤ η`;
3. has `|G_{d,η}| ≤ (C/η)^d` with the universal constant `C = 4e`;
4. (face version, A.6) for every coordinate set `𝒜`, every `q* ∈ 𝒜` and every `w ∈ Δ_d`
   supported on `𝒜`, the face rounding `g` of `w` (remaining mass at `q*`) lies in `G_{d,η}`,
   vanishes outside `𝒜`, and `‖w − g‖₁ ≤ η`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Lemma 6, p.10: "Let d ≥ 1, 0 < η ≤ 1 and
denote ∆d the (d − 1)-dimensional probability simplex in R^d. There is a finite grid Gd,η ⊂ ∆d such
that for every w ∈ ∆d, there is a rounding point g ∈ Gd,η with ∥w − g∥1 ≤ η, and |Gd,η| ≤ (C/η)^d for
some universal constant C." App. A.6, p.17: "Thus we may take C = 4e. For a nonempty admissible set
Ah(u) of size k ≤ d, use the same lattice grid restricted to that simplex face. … The result
belongs to Gh(u) and has ℓ1 error at most 2(k − 1)/n ≤ η".

**Formalization Note.** Stated for the explicit grid and rounding of A.6, with `C = 4e`, for
every choice of the coordinate receiving the remaining mass, and for any finite coordinate type `ι` (`ι = Fin d` is `ℝ^d`; the planner uses `ι = Q`). -/
theorem lemma_6 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ 1) :
    (∀ g ∈ latticeGrid ι η, IsDist g) ∧
    (∀ w : ι → ℝ, IsDist w → ∃ g ∈ latticeGrid ι η, ∑ i, |w i - g i| ≤ η) ∧
    ((latticeGrid ι η).card : ℝ) ≤ (4 * Real.exp 1 / η) ^ Fintype.card ι ∧
    (∀ 𝒜 : Finset ι, ∀ qstar ∈ 𝒜, ∀ w : ι → ℝ, IsDist w → (∀ i, i ∉ 𝒜 → w i = 0) →
      roundToFace η 𝒜 qstar w ∈ latticeGrid ι η ∧ (∀ i, i ∉ 𝒜 → roundToFace η 𝒜 qstar w i = 0) ∧
      ∑ i, |w i - roundToFace η 𝒜 qstar w i| ≤ η) := by sorry

end DecodablePOMDP
