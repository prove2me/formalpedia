-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_labelled_relation_count
-- name    : BirthdayEntropy.Soundness.labelled_relation_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T00:48:11.342707+00:00
-- url     : https://prove2.me/theorems/42ddf631-9464-4ff2-94eb-ccc7e8c7f698
-- title:
--   Labelled biclique counting for a finite relation
-- statement:
--   Let $V$ be a finite nonempty set, let $R$ be any binary relation on $V$, and let $r$ be a nonnegative integer. Sample all entries of two ordered $r$-tuples independently and uniformly from $V$. If $q$ is the probability that a uniform ordered pair belongs to $R$, then
--
--   $$q^{r^2}\le\Pr[\forall i,j,\ R(L_i,R_j)].$$
--
--   This is the labelled biclique lower bound in the ordered-pair normalization, which also applies to nonsymmetric relations. Repeated entries within either tuple are permitted. At $r=0$, both sides equal one. Applied to a loopless undirected graph on at least two vertices, the ordered-pair edge probability is at least half of the unordered edge density, yielding the bound used to pass from biclique soundness to selected density.
-- source:
--   Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, §4 PDF p6 / printed p5 (labelled bicliques ingredient attributed to Alon [Alo02]), and Corollary 4.10, PDF pp15–16 / printed pp14–15. Generalization to an arbitrary binary relation by the same two finite Jensen inequalities.

import Mathlib
noncomputable section
open scoped Classical

theorem BirthdayEntropy.Soundness.labelled_relation_count {V : Type*} [Fintype V] [Nonempty V] (R : V → V → Prop) (r : ℕ) :
    (((Finset.univ.filter (fun z : V × V => R z.1 z.2)).card : ℝ) /
      (Fintype.card V : ℝ)^2)^(r*r) ≤
    ((Finset.univ.filter (fun z : (Fin r → V) × (Fin r → V) =>
      ∀ i j, R (z.1 i) (z.2 j))).card : ℝ) / (Fintype.card V : ℝ)^(2*r) := by sorry
