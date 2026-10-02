-- Prove2me | Theorems.Thm_CookPvsNP_comp_run_bound
-- name    : CookPvsNP.comp_run_bound
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T09:11:59.463966+00:00
-- url     : https://prove2.me/theorems/fdc08e15-a750-4189-8a95-ced752fb92c7
-- title:
--   The Cook composite computes finite source runs with linear overhead
-- statement:
--   Suppose the first source halts on $x$ within $n_1$ steps and outputs $y$, and the second halts on $y$ within $n_2$ steps and outputs $z$, with ordinary word encodings. The original composite machine halts on the embedded $x$ and outputs the embedded $z$ at some time $t\le20(|x|+n_1+n_2+1)$. All setup, translation, simulation, and cleanup transitions are included; the original machine and output convention are unchanged.
-- source:
--   New auxiliary result derived from Sneed's exact published Prove2Me definition CookPvsNP_comp_machine, id 9c26b5f3-2f9d-4c5d-9194-692cbc786b4a (2026-09-30), without changing its transitions. It supports the existing CookPvsNP.tm_compose_poly_witness for the scheduling-hardness mission. The underlying one-tape machine model is Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This particular representation and its equations are new formalization lemmas, not numbered claims of that paper.

import Definitions.Def_CookPvsNP_comp_machine

namespace CookPvsNP
theorem comp_run_bound {I S O A B : Type} [Fintype A] [Fintype B]
    (ι : I ↪ A) (j₁ : S ↪ A) (j₂ : S ↪ B) (κ : O ↪ B)
    (M₁ : TM A) (M₂ : TM B) (x : List I) (y : List S) (z : List O) (n₁ n₂ : ℕ)
    (h₁ : M₁.HaltsWithin n₁ (x.map ι))
    (o₁ : M₁.output (M₁.run n₁ (M₁.init (x.map ι))) = y.map (some ∘ j₁))
    (h₂ : M₂.HaltsWithin n₂ (y.map j₂))
    (o₂ : M₂.output (M₂.run n₂ (M₂.init (y.map j₂))) = z.map (some ∘ κ)) :
    ∃ t ≤ 20 * (x.length + n₁ + n₂ + 1),
      (compTM j₁ j₂ M₁ M₂).HaltsWithin t (x.map (compInputEmbedding ι)) ∧
      (compTM j₁ j₂ M₁ M₂).output
        ((compTM j₁ j₂ M₁ M₂).run t ((compTM j₁ j₂ M₁ M₂).init
          (x.map (compInputEmbedding ι)))) = z.map (some ∘ compOutputEmbedding κ) := by sorry
end CookPvsNP
