-- Prove2me | Theorems.Thm_Esquisse_galois_action_faithful_on_belyi_polynomials
-- name    : Esquisse.galois_action_faithful_on_belyi_polynomials
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T22:02:38.653629+00:00
-- url     : https://prove2.me/theorems/92738160-f653-40ce-aaf0-99af4750ad2b
-- title:
--   $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acts faithfully on dessins d'enfants (plane trees)
-- statement:
--   Let $\gamma$ be a non-identity element of $\Gamma = \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$. Then there exists a Belyi polynomial $P \in \overline{\mathbb{Q}}[X]$ — a nonconstant polynomial all of whose critical values lie in $\{0,1\}$ — such that $P$ and its conjugate $P^{\gamma}$, obtained by applying $\gamma$ to the coefficients of $P$, are **not** affinely equivalent: there are no $a \neq 0$ and $b$ in $\overline{\mathbb{Q}}$ with $P^{\gamma}(X) = P(aX + b)$.
--
--   Since affine equivalence of Belyi polynomials is exactly isomorphism of the associated plane trees $P^{-1}([0,1])$, the statement says that no nontrivial element of the absolute Galois group fixes every dessin d'enfant: the action of $\Gamma$ on dessins is faithful, already on the subclass of trees. This is the elementary form of the faithfulness assertion of the Esquisse, where it is stated for the outer action of $\Gamma$ on the profinite fundamental group $\hat{\pi}_{0,3}$ of $\mathbb{P}^1 \smallsetminus \{0,1,\infty\}$; the tree-level sharpening is due to Lenstra. Nothing is claimed about the degree of $P$ or about how it depends on $\gamma$.
-- source:
--   A. Grothendieck, Esquisse d'un Programme (1984), published in Geometric Galois Actions 1, LMS Lecture Note Series 242, CUP 1997, §2, p. 9 of the French text: « cette opération est fidèle — à vrai dire, elle est fidèle déjà sur le premier étage non trivial de cette tour, à savoir $\hat{T}_{0,4}$ — ce qui signifie aussi, essentiellement, que l'action extérieure de $\Gamma$ sur le groupe fondamental $\hat{\pi}_{0,3}$ de la droite projective standard $\mathbb{P}^1$ sur $\overline{\mathbb{Q}}$, privée des trois points $0$, $1$, $\infty$, est déjà fidèle »; together with §3, pp. 15-16 (the Galois action on maps by conjugating the coefficients). Tree-level form: H. W. Lenstra, appendix to L. Schneps (ed.), The Grothendieck Theory of Dessins d'Enfants, LMS Lecture Note Series 200, CUP 1994.

import Mathlib
import Definitions.Def_esquisse_dessins_basic

open Polynomial

open Polynomial

namespace Esquisse

theorem galois_action_faithful_on_belyi_polynomials (γ : GaloisQ) (hγ : γ ≠ 1) :
    ∃ P : Polynomial AlgNum, IsBelyiPolynomial P ∧ ¬ AffineEquivalent P (galoisConj γ P) := by sorry

end Esquisse
