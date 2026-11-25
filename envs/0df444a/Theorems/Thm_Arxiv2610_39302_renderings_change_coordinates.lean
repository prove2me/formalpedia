-- Prove2me | Theorems.Thm_Arxiv2610_39302_renderings_change_coordinates
-- name    : Arxiv2610_39302.renderings_change_coordinates
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T02:56:43.090655+00:00
-- url     : https://prove2.me/theorems/30edebda-dac5-4b1b-ac4e-0ee52e73a801
-- title:
--   Lemma 1: renderings only change coordinates
-- statement:
--   Let $Z$ be a finite world with probabilities $p(z)>0$, let $\pi$ be a positive-pair law with marginals $p$, and let $\ell$, $\Omega$ satisfy the standing assumptions of Section 2.1. Let a modality render the world through an injective map $g:Z\to X$. Then:
--
--   1. composing with $g$, $f\mapsto f\circ g$, is a bijection from encoders $f:g(Z)\to\mathbb{R}^k$ on the image $g(Z)$ onto functions $Z\to\mathbb{R}^k$;
--   2. for every encoder $f:X\to\mathbb{R}^k$,
--
--   $$L_m(f)=L_\pi(f\circ g).$$
--
--   The training problem of a modality is therefore the world-state problem written in other coordinates.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c001; Section 2.1 (stated inline) and Appendix A.2, Lemma 1, eq. (1), PDF pp. 3, 20

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem renderings_change_coordinates {Z X : Type*} [Fintype Z] {k : ℕ}
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π)
    (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (Om : Measure (Fin k → ℝ) → EReal)
    (hObj : IsJEPAObjective p ℓ Om) (g : Z → X) (hg : Function.Injective g) :
    Function.Bijective
      (fun (f : Set.range g → Fin k → ℝ) (z : Z) => f ⟨g z, Set.mem_range_self z⟩) ∧
    ∀ f : X → Fin k → ℝ, modalityLoss p π ℓ Om g f = worldLoss p π ℓ Om (fun z => f (g z)) := by sorry

end Arxiv2610_39302
