-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_lemma13
-- name    : ExactSDPDuality.ELSD.lemma13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:16:57.924826+00:00
-- url     : https://prove2.me/theorems/ed5bd3a9-62db-4cdb-bf58-62ddfe93fdbd
-- title:
--   Lemma 13 — if 0 ∈ G then G° = Cl(G*)
-- statement:
--   Let $Q_0,\dots,Q_m$ be real symmetric $n\times n$ matrices and $G = \{x\in\mathbb R^m\mid Q(x)\succeq 0\}$. Let $G^\circ = \{y\mid x^{\mathsf T}y\le 1\ \forall x\in G\}$ be the polar of $G$ and $G^* = \{Q^*(U)\mid U\bullet Q_0\le 1,\ U\succeq 0\}$ its algebraic polar. If $0\in G$, then
--   $$G^\circ = \mathrm{Cl}(G^*),$$
--   the closure in $\mathbb R^m$.
--
--   The algebraic polar is thus a description of the polar up to closure; the gap between $G^*$ and its closure is what the sets $\mathcal W_k$ repair.
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 143, Lemma 13

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Lemma 13 (Ramana 1997, p. 143): if `0 ∈ G`, then `G° = Cl(G*)`. -/
theorem lemma13 {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q) :
    polar (feasibleSet Q0 Q) = closure (algPolar Q0 Q) := by sorry

end ExactSDPDuality.ELSD
