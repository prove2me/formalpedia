-- Prove2me | Theorems.Thm_CoDecompFO_codeFold_simulation
-- name    : CoDecompFO.codeFold_simulation
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:21:02.671834+00:00
-- url     : https://prove2.me/theorems/c10bb372-3a32-4aec-83ad-c935436bf82b
-- title:
--   Local numeric hypothetical operations simulate the bottom-up semantic fold
-- statement:
--   Fix a first-order sentence $\varphi$, a width bound $w$, and a numeric bound $C$. Suppose that numeric tables are decoded as $(2\ell,\ell)$-hypotheticals over the bags with the equality relation adjoined, where $\ell$ is the quantifier count of $\varphi$. Assume three local properties: the numeric leaf operation encodes the induced hypothetical of the full strategy; the numeric join operation encodes the projection of the reduced pullback over the adhesion; and every hypothetical over at most $w$ points has code at most $C$.
--
--   Then every numeric bottom-up computation on a tree co-decomposition of width at most $w$ has value at most $C$ and is simulated by the semantic bottom-up computation of hypotheticals. More precisely, its value is the code of a hypothetical produced by `CoDecomp.IsFold` on exactly the same node and set of absorbed nodes.
--
--   This is the induction underlying the algorithmic use of Observation 5.79: the leaf and reduced-pullback recurrences are local, while this statement lifts them uniformly through an arbitrary rooted tree. It separates the construction of concrete primitive-recursive codecs from the semantic correctness of the tree fold.
--
--   **Formalization Note** The numeric computation is `CoDecomp.CodeFold`; the semantic computation takes place on `T.withEq`. In a join, $g$ is the map from the child bag, $h$ the map from the parent bag, and the child's hypothetical is the first argument of `pb`, matching the published definitions.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), Observation 5.79 and ¶5.80 with Lemma 5.81, PDF p.43 (printed p.41); numeric/semantic simulation needed for proof of Theorem 1.16, ibid.

import Mathlib
import Definitions.Def_CoDecompFO_AltMatrix
import Definitions.Def_CoDecompFO_Fold
import Definitions.Def_CoDecompFO_CodeFold
import Definitions.Def_CoDecompFO_Codes

set_option autoImplicit false

open FirstOrder
open CoDecompFO

/-- Local numeric implementations of the induced table and of the reduced pullback lift to a
simulation of the whole bottom-up computation. -/
theorem CoDecompFO.codeFold_simulation (σ : Sig) (φ : σ.lang.Sentence) (w C : ℕ)
    (leaf join : List ℕ → ℕ)
    (code : ∀ {n : ℕ}, HTh (sigmaEq σ) (Fin n) (2 * quantCount φ) (quantCount φ) → ℕ)
    (hleaf : ∀ B : Bag σ,
      code (ind (sigmaEq σ) (2 * quantCount φ) (quantCount φ)
        (Strat.full (Fin B.withEq.n) (quantCount φ)) []) =
        leaf (frame [encF φ, encBag B]))
    (hjoin : ∀ (A D K : Bag σ) (g : Fin D.n → Fin K.n) (h : Fin A.n → Fin K.n)
      (H : HTh (sigmaEq σ) (Fin A.n) (2 * quantCount φ) (quantCount φ))
      (Hc : HTh (sigmaEq σ) (Fin D.n) (2 * quantCount φ) (quantCount φ)),
      code (push (Fib.snd : Fib g h → Fin A.n) (quantCount φ) (pb g h (quantCount φ) Hc H)) =
        join (frame [encF φ, encBag A, encBag D, encBag K,
          List.ofFn (fun x => (h x).val), List.ofFn (fun x => (g x).val),
          [code H], [code Hc] ]))
    (hcode : ∀ (n : ℕ) (H : HTh (sigmaEq σ) (Fin n) (2 * quantCount φ) (quantCount φ)),
      n ≤ w → code H ≤ C) :
    ∀ (T : CoDecomp σ), width T ≤ w →
      ∀ (r t : Fin T.b) (S : Set (Fin T.b)) (v : ℕ),
        T.CodeFold r (encF φ) leaf join t S v →
        v ≤ C ∧ ∃ H : HTh (sigmaEq σ) (Fin (T.withEq.bag t).n)
          (2 * quantCount φ) (quantCount φ),
          T.withEq.IsFold r (2 * quantCount φ) (quantCount φ) t S H ∧ code H = v := by sorry
