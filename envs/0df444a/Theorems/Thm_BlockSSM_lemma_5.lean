-- Prove2me | Theorems.Thm_BlockSSM_lemma_5
-- name    : BlockSSM.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:27:45.633811+00:00
-- url     : https://prove2.me/theorems/cd28fb4a-9a33-4c70-9322-4f3176a22251
-- title:
--   Lemma 5: finite transition monoid
-- statement:
--   Fix a finite group $G$ and a finite-state tracker of $G$ with reachable set $R$, whose decoder tracks $G$, and put $V=\mathrm{aff}(R)$. Then:
--
--   1. the restrictions $F_s|_V$ of the word maps to $V$ form a finite monoid $M$;
--   2. the rule $F_s|_V\mapsto\pi(s)$ is a well-defined surjective monoid homomorphism $\pi:M\twoheadrightarrow G$.
--
--   This is the first of the three steps of the lower bound: it replaces the possibly singular dynamics by a finite algebraic object that remembers the group.
--
--   **Formalization Note** "Well-defined" is carried by the existence of a homomorphism taking the value $\pi(s)$ at $F_s|_V$ for every word $s$. Multiplication in $M$ is composition, under which the later word's product multiplies on the left.
--
--   Differences from the source:
--   - generalization: an integer block bound $b\ge 1$ → an arbitrary $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`); reason: every integer $b\ge 1$ is a case through the cast; the lemma does not use $b\ge 1$
--   - encoding: hidden state space $\mathbb C^n$ with block-diagonal $A_g$ → the product $\prod_i\mathbb C^{n_i}$ with one matrix per block; reason: the same space split along the partition; the linear part is block-diagonal by construction
--   - encoding: a word $s=g_1\cdots g_T$ → a list with $g_1$ at the head; reason: the same words; the empty list is the empty word
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 5, p.3 (PDF p.4); §3.2 lead-in, p.3

import Mathlib
import Definitions.Def_BlockSSM_Tracker_Tracks
import Definitions.Def_BlockSSM_Tracker_transMonoid

universe u

namespace BlockSSM

/-- **Lemma 5 (Finite transition monoid).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Lemma 5, p.3 (PDF p.4): "The restrictions of word
maps to V form a finite monoid M. The rule F_s|_V ↦ π(s) is a well-defined surjective homomorphism
π : M ↠ G." The standing assumption is the lead-in of §3.2: "Fix a finite-state tracker of dimension
n, and put V = aff(R)."

**Formalization Note.** "Well-defined" is carried by the existence of the homomorphism `p` with the
displayed value on every word: if `F_s|_V = F_{s'}|_V`, then `π(s) = π(s')`. `Function.End`
multiplication is composition, so `F_t|_V * F_s|_V = F_{st}|_V` and `π(st) = π(t) π(s)`: this is a
homomorphism, not an anti-homomorphism. -/
theorem lemma_5 {G : Type u} [Group G] [Finite G] {b : ℕ∞} (T : Tracker G b) (ht : T.Tracks)
    (hf : T.IsFiniteState) :
    Finite T.transMonoid ∧ ∃ p : T.transMonoid →* G, Function.Surjective p ∧
      ∀ s : List G, p (T.wordElt s) = wordProd s := by sorry

end BlockSSM
