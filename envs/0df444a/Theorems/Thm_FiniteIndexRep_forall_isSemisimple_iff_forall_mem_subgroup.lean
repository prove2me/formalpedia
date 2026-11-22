-- Prove2me | Theorems.Thm_FiniteIndexRep_forall_isSemisimple_iff_forall_mem_subgroup
-- name    : FiniteIndexRep.forall_isSemisimple_iff_forall_mem_subgroup
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:48:55.666845+00:00
-- url     : https://prove2.me/theorems/0c495d7b-cb11-420d-b2ac-2fb4f3cd23a4
-- title:
--   Every $\rho(g)$ is semisimple iff every $\rho(h)$, $h\in H$, is semisimple, for $H$ of finite index (characteristic $0$, finite dimension)
-- statement:
--   **Elementwise semisimplicity is detected on a subgroup of finite index.** Let $k$ be a field of characteristic $0$, let $G$ be a group and $H\le G$ a subgroup of finite index, and let $\rho\colon G\to\mathrm{GL}(V)$ be a representation on a finite-dimensional $k$-vector space $V$. An endomorphism $T$ of $V$ is *semisimple* if every $T$-stable subspace has a $T$-stable complement. Over a field of characteristic $0$ this holds iff the minimal polynomial of $T$ is squarefree, that is, iff $T$ is diagonalizable over an algebraic closure of $k$. Then
--   $$\rho(g)\ \text{is semisimple for every } g\in G\iff\rho(h)\ \text{is semisimple for every } h\in H.$$
--
--   In the theory of Weil groups, after Langlands and Weil (and in §14.1.1 of the source, p. 526), a representation of a local or global Weil group is required to send every element to a semisimple element of $\mathrm{GL}(V)$. The statement shows that this condition can be checked on any open subgroup of finite index, such as $W_E\subset W_F$. The source uses it in the proof of Proposition 14.1.1.1(5)(c), citing Langlands, to show that every element of $W_F$ acts semisimply on $\mathrm{Ind}_{W_E}^{W_F}(\rho)$ when $\rho$ is one-dimensional.
--
--   **Formalization Note.** Semisimplicity of an endomorphism is Mathlib's `Module.End.IsSemisimple` (the $k[X]$-module structure defined by the endomorphism is semisimple). The source works over $\mathbb C$ with continuous representations. Here $k$ is any field of characteristic $0$, and continuity is irrelevant. The hypothesis on the characteristic is necessary: in characteristic $p$, the group $G=\mathbb Z$ acting through a unipotent Jordan block $\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$ gives a counterexample with $H=p\mathbb Z$, which acts trivially.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 526, proof of Proposition 14.1.1.1(5)(c) and the convention, stated at the end of p. 526, that representations of Weil groups send each element to a semisimple element; classical reference: R. P. Langlands, On the Functional Equation of the Artin L-Functions, unpublished preprint, 1970, Ch. 1, Lemma 1.1, p. 5 (as cited by the paper at that spot)

import Mathlib

set_option autoImplicit false

namespace FiniteIndexRep

/-- In characteristic zero, every element of `G` acts by a semisimple endomorphism in a
finite-dimensional representation iff every element of a subgroup `H` of finite index does. -/
theorem forall_isSemisimple_iff_forall_mem_subgroup {k G V : Type*} [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (ρ : Representation k G V) (H : Subgroup G) [H.FiniteIndex] :
    (∀ g : G, Module.End.IsSemisimple (ρ g)) ↔ ∀ h ∈ H, Module.End.IsSemisimple (ρ h) := by
  sorry

end FiniteIndexRep
