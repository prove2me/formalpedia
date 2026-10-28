-- Prove2me | Theorems.Thm_DealerDissem_RankFree_lemma_A_2
-- name    : DealerDissem.RankFree.lemma_A_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:23.516369+00:00
-- url     : https://prove2.me/theorems/200b08a1-00ce-46d3-9ff8-d160a1b48158
-- title:
--   Lemma A.2, p. 41 — for $f$ non-decreasing and $q$-Lipschitz on $\mathbb R_+$, $\min(pv,y)+f(pv-\omega)\le pv+f(y-\omega)$
-- statement:
--   Let $q\in(0,1)$ and let $f$ be a non-decreasing function on $\mathbb R_+$ that is Lipschitz with constant $q$ there. Then for all reals $p,v,y,\omega$ with $\omega\le pv$ and $\omega\le y$,
--   $$\min(pv,y)+f(pv-\omega)\le pv+f(y-\omega).$$
--
--   The lemma is applied to $f=\Omega$ in point 2 of the proof of Theorem 2, to compare an arbitrary offer with the target's financing needs.
--
--   **Formalization Note.** $q$ is the availability probability of the model, so $0<q<1$ is the paper's standing assumption (the inequality is false for $q>1$). "Defined over $\mathbb R_+$" is encoded by imposing monotonicity and the Lipschitz bound on $[0,\infty)$ only; the hypotheses $\omega\le pv$ and $\omega\le y$ ensure $f$ is evaluated at non-negative points. No sign is imposed on $p$, $v$ or $\omega$; the statement is the paper's for every value it allows.
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), p. 41 (PDF 43), Lemma A.2 (proved in the Online Appendix)

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Lemma A.2, p. 41: for `f` non-decreasing and `q`-Lipschitz on `ℝ₊`, and `ω ≤ p v`,
`ω ≤ y`: `min(p v, y) + f(p v − ω) ≤ p v + f(y − ω)`. -/
theorem lemma_A_2 (P : Params) (f : ℝ → ℝ) (hf_mono : MonotoneOn f (Set.Ici 0))
    (hf_lip : ∀ x x', 0 ≤ x → 0 ≤ x' → |f x - f x'| ≤ P.q * |x - x'|)
    (p v y ω : ℝ) (hωpv : ω ≤ p * v) (hωy : ω ≤ y) :
    min (p * v) y + f (p * v - ω) ≤ p * v + f (y - ω) := by sorry

end DealerDissem.RankFree
