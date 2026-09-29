-- Prove2me | Theorems.Thm_Esquisse_belyi_polynomial_separating_algebraic_number
-- name    : Esquisse.belyi_polynomial_separating_algebraic_number
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T22:01:48.772148+00:00
-- url     : https://prove2.me/theorems/31fdddff-b311-43a6-b100-82df1d582e79
-- title:
--   Separation: for each algebraic number $\alpha$ there is a tree whose class is fixed only by automorphisms fixing $\alpha$
-- statement:
--   For every algebraic number $\alpha \in \overline{\mathbb{Q}}$ there is a Belyi polynomial $P \in \overline{\mathbb{Q}}[X]$ such that every $\gamma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with $P^{\gamma}$ affinely equivalent to $P$ satisfies $\gamma(\alpha) = \alpha$.
--
--   Equivalently: the field of moduli of the dessin defined by $P$ — the fixed field of the stabiliser of its affine equivalence class — contains $\alpha$. This is the separation statement from which faithfulness of the Galois action on plane trees follows immediately: given $\gamma \neq 1$, choose $\alpha$ with $\gamma(\alpha) \neq \alpha$ and the corresponding $P$ is a tree moved by $\gamma$. Only one direction is asserted; it is not claimed that every automorphism fixing $\alpha$ preserves the class of $P$, nor that the field of moduli equals $\mathbb{Q}(\alpha)$.
-- source:
--   A. Grothendieck, Esquisse d'un Programme (1984), published in Geometric Galois Actions 1, LMS Lecture Note Series 242, CUP 1997, §2, p. 9 (faithfulness of the outer action of $\Gamma$) and §3, title and pp. 15-17 (the number field attached to a dessin). Tree-level form: H. W. Lenstra, appendix to L. Schneps (ed.), The Grothendieck Theory of Dessins d'Enfants, LMS Lecture Note Series 200, CUP 1994.

import Mathlib
import Definitions.Def_esquisse_dessins_basic

open Polynomial

open Polynomial

namespace Esquisse

theorem belyi_polynomial_separating_algebraic_number (α : AlgNum) :
    ∃ P : Polynomial AlgNum, IsBelyiPolynomial P ∧
      ∀ γ : GaloisQ, AffineEquivalent P (galoisConj γ P) → γ α = α := by sorry

end Esquisse
