-- Prove2me | Theorems.Thm_Esquisse_galois_orbit_of_polynomial_finite
-- name    : Esquisse.galois_orbit_of_polynomial_finite
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:59:23.463691+00:00
-- url     : https://prove2.me/theorems/0a60006a-b9c2-4128-9ab8-0ad08f0e0e8e
-- title:
--   A polynomial over $\overline{\mathbb{Q}}$ has only finitely many Galois conjugates
-- statement:
--   For every polynomial $P \in \overline{\mathbb{Q}}[X]$, the set of its Galois conjugates
--   $$\{\,P^{\gamma} \;:\; \gamma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})\,\}$$
--   is finite, where $P^{\gamma}$ denotes coefficientwise application of $\gamma$.
--
--   The reason is that the finitely many coefficients of $P$ generate a number field $K$, and the conjugates of $P$ are indexed by the finitely many embeddings of $K$ into $\overline{\mathbb{Q}}$. For a dessin this is the assertion, made in passing in §3 of the Esquisse, that a given oriented map has only finitely many conjugates, so that the Galois orbit of a dessin — and with it the number field attached to the dessin, the fixed field of its stabiliser — is a finite object. No hypothesis is placed on $P$; in particular it need not be a Belyi polynomial.
-- source:
--   A. Grothendieck, Esquisse d'un Programme (1984), published in Geometric Galois Actions 1, LMS Lecture Note Series 242, CUP 1997, §3, p. 16 of the French text: « quelles exactement sont les conjuguées de telle carte orientée donnée ? (il y en a, visiblement, un nombre fini seulement) »; and §3's title, « Corps de nombres associés à un dessin d'enfant ».

import Mathlib
import Definitions.Def_esquisse_dessins_basic

open Polynomial

open Polynomial

namespace Esquisse

theorem galois_orbit_of_polynomial_finite (P : Polynomial AlgNum) :
    (Set.range (fun γ : GaloisQ => galoisConj γ P)).Finite := by sorry

end Esquisse
