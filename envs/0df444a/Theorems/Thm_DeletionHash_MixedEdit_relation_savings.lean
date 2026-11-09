-- Prove2me | Theorems.Thm_DeletionHash_MixedEdit_relation_savings
-- name    : DeletionHash.MixedEdit.relation_savings
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:26.448272+00:00
-- url     : https://prove2.me/theorems/6c22af30-8f12-4738-9551-bc49f683a11d
-- title:
--   Lemma 4.2 — relation savings
-- statement:
--   In the standing proof regime let $I$ be a finite set of catalogue rules and let $w\in K_0$ satisfy $\overline w=\sum_{g\in I}\overline g$. Then
--   $$c(I)\le t|I|+t,\qquad |I|\ge2\ \Longrightarrow\ c(I)\le(2t-1)|I|.$$
--   The support union does not cancel edges, and $w$ is not adjoined to $I$ in the component count. No independence assumption is imposed. Both component savings are retained for use in the witness argument.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §§2.2–6 → Regime: q≥2, t≥2, b≥1, k=2 ceil(log_q n)+2, L=3(k+b+1), b<k, L≤n; reason: the section preamble is explicit in each applicable signature
--   - encoding: undirected support components and a relation modulo two → a finite incident-vertex graph, and coordinate casts to ZMod 2; reason: the graph discards other isolated vertices and keeps union supports without cancellation
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Lemma 4.2, printed p. 12 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_SupportComponents
import Definitions.Def_DeletionHash_MixedEdit_Regime

namespace DeletionHash.MixedEdit

universe u

/-- Lemma 4.2: no linear independence premise is imposed. -/
theorem relation_savings {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (I : Finset (Spectrum α L)) (hI : ∀ g ∈ I, g ∈ Catalogue k L t b)
    (w : Spectrum α L) (hw : w ∈ Catalogue k L t b)
    (hrel : parity w = ∑ g ∈ I, parity g) :
    componentCount I ≤ t*I.card+t ∧ (2 ≤ I.card → componentCount I ≤ (2*t-1)*I.card) := by sorry

end DeletionHash.MixedEdit
