-- Prove2me | Theorems.Thm_FiniteIndexRep_isSemisimple_ind_apply
-- name    : FiniteIndexRep.isSemisimple_ind_apply
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:49:03.358026+00:00
-- url     : https://prove2.me/theorems/3e27cf01-15a6-4975-9be5-400537d0b4f9
-- title:
--   If every $\sigma(h)$ is semisimple, then every element of $G$ acts semisimply on $\mathrm{Ind}_H^G\sigma$ ($[G:H]<\infty$, characteristic $0$)
-- statement:
--   **Induction preserves elementwise semisimplicity.** Let $k$ be a field of characteristic $0$, let $G$ be a group and $H\le G$ a subgroup of finite index, and let $\sigma\colon H\to\mathrm{GL}(V)$ be a representation on a finite-dimensional $k$-vector space $V$ such that $\sigma(h)$ is a semisimple endomorphism of $V$ for every $h\in H$. Semisimple means diagonalizable over an algebraic closure of $k$. Let $\mathrm{Ind}_H^G(\sigma)=k[G]\otimes_{k[H]}V$ be the induced representation. Then for every $g\in G$,
--   $$\mathrm{Ind}_H^G(\sigma)(g)\ \text{is a semisimple endomorphism of } \mathrm{Ind}_H^G(V).$$
--   In particular this holds for every one-dimensional $\sigma$, that is, for every character $\sigma\colon H\to k^\times$.
--
--   The one-dimensional case is Proposition 14.1.1.1(5)(c) of the source. There $G=W_F$ is a Weil group and $H=W_E$ is the open subgroup of finite index attached to a finite separable extension $E/F$. It shows that representations induced from Hecke characters satisfy Weil's and Langlands' standing condition that every element acts semisimply. The source uses this in §14.1.2 for the representations $\mathrm{Ind}_{W_{F'/F}}^{W_{F'/\mathbb Q}}(\chi')$.
--
--   **Formalization Note.** The induced representation is Mathlib's `Representation.ind H.subtype σ`, the coinvariants $(k[G]\otimes_k V)_H$, which is the induced representation (left adjoint to restriction). Semisimplicity of an endomorphism is `Module.End.IsSemisimple`. The source has $k=\mathbb C$, continuous representations of Weil groups, and $\sigma$ one-dimensional (the restriction to $W_E$ of a character of $W_F$). The statement here is more general: $\sigma$ is any finite-dimensional representation of $H$ whose elements act semisimply. Every one-dimensional $\sigma$ satisfies this hypothesis.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 525, Proposition 14.1.1.1(5)(c) (proof on p. 526), stated for an arbitrary group, subgroup of finite index and representation of the subgroup whose elements act semisimply; classical reference: R. P. Langlands, On the Functional Equation of the Artin L-Functions, unpublished preprint, 1970, Ch. 1, Lemma 1.1, p. 5 (as cited by the paper at that spot)

import Mathlib

set_option autoImplicit false

namespace FiniteIndexRep

/-- In characteristic zero, if every element of a subgroup `H` of finite index of `G` acts by a
semisimple endomorphism in a finite-dimensional representation `σ` of `H`, then every element of `G`
acts by a semisimple endomorphism on the induced representation. -/
theorem isSemisimple_ind_apply {k G V : Type*} [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (H : Subgroup G) [H.FiniteIndex] (σ : Representation k H V)
    (hσ : ∀ h : H, Module.End.IsSemisimple (σ h)) (g : G) :
    Module.End.IsSemisimple (Representation.ind H.subtype σ g) := by
  sorry

end FiniteIndexRep
