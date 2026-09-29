-- Prove2me | Theorems.Thm_BurauFaithful_burau_three_kernel_word_criterion
-- name    : BurauFaithful.burau_three_kernel_word_criterion
-- status  : Open
-- author  : @lt9
-- created : 2026-09-28T17:33:09.730677+00:00
-- url     : https://prove2.me/theorems/e1d4bdd7-7967-44d8-91b8-b0c88eb1a843
-- title:
--   Magnus–Peluso, word form: the kernel of the 3-strand Burau representation is the normal closure of the braid relation
-- statement:
--   This is the algebraic core of the Magnus--Peluso theorem, recast as a statement about words.
--
--   Let $B_3 = \langle \sigma_1, \sigma_2 \mid \sigma_1\sigma_2\sigma_1 = \sigma_2\sigma_1\sigma_2\rangle$ be Artin's braid group on three strands, presented as a quotient of the free group $F_2$ on the two generators, and let
--
--   $$\rho_3 : B_3 \longrightarrow \mathrm{GL}_3(\mathbb{Z}[t,t^{-1}])$$
--
--   be the unreduced Burau representation, so that $\sigma_1 \mapsto \begin{pmatrix} 1-t & t & 0 \\ 1 & 0 & 0 \\ 0 & 0 & 1\end{pmatrix}$ and $\sigma_2 \mapsto \begin{pmatrix} 1 & 0 & 0 \\ 0 & 1-t & t \\ 0 & 1 & 0\end{pmatrix}$. Write
--
--   $$r = \sigma_1\sigma_2\sigma_1(\sigma_2\sigma_1\sigma_2)^{-1} \in F_2$$
--
--   for the single defining relation of $B_3$, viewed as an element of the free group. The theorem asserts that for every word $w \in F_2$,
--
--   $$\rho_3(\overline{w}) = I_3 \quad\Longleftrightarrow\quad w \in \langle\!\langle r \rangle\!\rangle ,$$
--
--   where $\overline{w}$ is the image of $w$ in $B_3$ and $\langle\!\langle r\rangle\!\rangle$ is the normal closure of $r$ in $F_2$, that is, the kernel of the quotient map $F_2 \to B_3$.
--
--   The statement isolates the exact algebraic content of faithfulness: an element of the kernel of $\rho_3$ is visible on the level of words *only* through the braid relation, so the kernel of the word-level representation is precisely the presentation kernel. Equivalently, $\rho_3$ induces an injective homomorphism $F_2/\langle\!\langle r\rangle\!\rangle \hookrightarrow \mathrm{GL}_3(\mathbb{Z}[t,t^{-1}])$. This is the three-strand case of the classical theorem of Magnus and Peluso (1969); it is the input used to deduce that $\rho_3$ itself is injective, since a braid in the kernel lifts to a word whose class lies in $\langle\!\langle r\rangle\!\rangle$ and is therefore trivial in $B_3$.
--
--   **Formalization Note** The braid group is the published `BraidsLinksMCG.ArtinBraidGroup 3`, a `PresentedGroup` on `Fin 2` with relations `BraidsLinksMCG.braidRels 3`; on two generators there is no commuting relation (the only pair of indices has distance $1$), so the relation set reduces to the single braid relation, and the statement is made for the free group on `Fin 2` with the relator `BurauFaithful.braidRel3` declared in the preamble. The backwards implication is functoriality of the representation ($r$ maps to $I_3$, hence so does every conjugate of $r$); the forwards implication is the substance of Magnus--Peluso.
-- source:
--   W. Magnus and A. Peluso, *On a theorem of V. I. Arnold*, Comm. Pure Appl. Math. 22 (1969), 689-692 (faithfulness of the Burau representation for n = 3); Vasudha Bharathram, Joan S. Birman, Tara E. Brendle, *The Burau representation is faithful for n = 4*, arXiv:2607.05283v2 (14 Sep 2026), https://arxiv.org/abs/2607.05283, Theorem 4.1 (Section 4)

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

namespace BurauFaithful

/-- The single Artin relation `σ₁σ₂σ₁(σ₂σ₁σ₂)⁻¹` of `B₃`, as a word in the free group on the
generators `σ₁`, `σ₂`. -/
def braidRel3 : FreeGroup (Fin 2) :=
  FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) *
    (FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2))⁻¹

end BurauFaithful

theorem BurauFaithful.burau_three_kernel_word_criterion (w : FreeGroup (Fin 2)) :
    BurauFaithful.burauRep 3 (PresentedGroup.mk (BraidsLinksMCG.braidRels 3) w) = 1 ↔
      w ∈ Subgroup.normalClosure ({BurauFaithful.braidRel3} : Set (FreeGroup (Fin 2))) := by sorry
