-- Prove2me | Theorems.Thm_CoffmanMitrani1980_Region_lemma2_tight_sets_nested
-- name    : CoffmanMitrani1980.Region.lemma2_tight_sets_nested
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:16:27.961299+00:00
-- url     : https://prove2.me/theorems/8903e4f0-b463-45b4-a55a-4b2ed4baff86
-- title:
--   Lemma 2, proof — the tight sets of a point of H** are nested
-- statement:
--   Fix the model parameters ($\lambda_i,\mu_i>0$, $\rho<1$) and let $W\in H^{**}$. Write $f(g)=\big(\sum_{i\in g}\rho_i/\mu_i\big)/\big(1-\sum_{i\in g}\rho_i\big)$. If $g_1$ and $g_2$ are nonempty sets of classes with
--   $$\sum_{i\in g_1}\rho_iW_i=f(g_1)\quad\text{and}\quad\sum_{i\in g_2}\rho_iW_i=f(g_2),$$
--   then $g_1\subseteq g_2$ or $g_2\subseteq g_1$.
--
--   This is the step of the proof of Lemma 2 showing that the $M$ sets of the system (5) satisfied by a vertex form a chain.
--
--   **Formalization Note.** The sets may be proper or equal to the full set of classes; for the full set the equality is the conservation law (1), since $f$ of the full set equals $V/(1-\rho)$.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), DOI 10.1287/opre.28.3.810, p. 818, Lemma 2, proof ("We shall demonstrate that all these subsets are strictly included in each other")

import Definitions.Def_CoffmanMitrani1980_Region_Model

open Finset

namespace CoffmanMitrani1980.Region

/-- Coffman and Mitrani, Operations Research 28 (1980), p. 818 (PDF 10), Lemma 2, proof: if a point
`W` of H\*\* satisfies (4) with equality for two nonempty sets of classes `g₁` and `g₂` (as in the
system (5)), then one of them is included in the other. (Otherwise `h₁ = g₁ - g₁₂` and `h₂ = g₂ - g₁₂`
are nonempty, and the paper derives a violation of (4) for `G₁₂ = g₁ ∪ g₂`.)

**Formalization Note.** Equality is `Σ_{i∈g} ρᵢ Wᵢ = f(g)`. For `g = univ` it is (1), since
`f(univ) = V/(1 - ρ)`; the sets may be proper or equal to `univ`, as in (5). -/
theorem lemma2_tight_sets_nested {M : ℕ} (p : Params M) (W : Fin M → ℝ) (hW : W ∈ p.Hss)
    (g₁ g₂ : Finset (Fin M)) (hg₁ : g₁.Nonempty) (hg₂ : g₂.Nonempty)
    (ht₁ : ∑ i ∈ g₁, p.rho i * W i = p.f g₁) (ht₂ : ∑ i ∈ g₂, p.rho i * W i = p.f g₂) :
    g₁ ⊆ g₂ ∨ g₂ ⊆ g₁ := by sorry

end CoffmanMitrani1980.Region
