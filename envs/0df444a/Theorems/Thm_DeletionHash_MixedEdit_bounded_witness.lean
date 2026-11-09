-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_bounded_witness
-- name    : DeletionHash.MixedEdit.bounded_witness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:23.096813+00:00
-- url     : https://prove2.me/theorems/e8f48648-30ab-47cd-bb7d-647c989349c2
-- title:
--   Lemma 4.6 — bounded witness
-- statement:
--   In the standing proof regime, fix $r\ge1$ and a hash $H$. If $x\in W_{n,k}\setminus E$ has a non-bipartite component in the actual equal-label confusability graph, then there is a generating sequence of surviving rules at $R_L(x)$ with length $R$ such that
--   $$2\le R\le M=1+2t(2L+2b-2)L,\qquad c(F)\le(2t-1)R+1.$$
--   If $R\le L$, then also $c(F)\le(2t-1)R$. The sequence has independent reductions and actual earlier suppliers for every negative gram absent from $x$; $F$ is its underlying set. This retains the sharper small-witness clause and every surviving-rule requirement.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
--   - encoding: a generating sequence F⊆K and its component count → a Fin R indexed sequence with surviving entries, and componentCount of its underlying ruleSet; reason: linear independence ensures distinct rules, so its length equals the cardinality of the underlying set
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 4.6, printed p. 14 (PDF p. 16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Generation
import Definitions.Def_DeletionHash_MixedEdit_ConflictGraph

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 4.6: survival, generation, both component bounds, and the exact size bound. -/
theorem bounded_witness {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L r : ℕ) (hreg : Regime (Fintype.card α) n t b k L) (hr : 1 ≤ r)
    (ξ : HashSample α L r) (x : Word α n) (hbad : BadComponent n k t b ξ x) :
    ∃ R : ℕ, ∃ G : Fin R → Spectrum α L,
      GeneratingSequence k t b (spectrum L (letters x)) G ∧ (∀ j, Survives k t b ξ (G j)) ∧
      2 ≤ R ∧ R ≤ witnessBound t b L ∧ componentCount (ruleSet G) ≤ (2*t-1)*R+1 ∧
      (R ≤ L → componentCount (ruleSet G) ≤ (2*t-1)*R) := by sorry

end DeletionHash.MixedEdit
