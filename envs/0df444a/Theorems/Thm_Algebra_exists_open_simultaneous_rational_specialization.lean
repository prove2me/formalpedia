-- Prove2me | Theorems.Thm_Algebra_exists_open_simultaneous_rational_specialization
-- name    : Algebra.exists_open_simultaneous_rational_specialization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T15:31:59.669605+00:00
-- url     : https://prove2.me/theorems/ba7cb73b-c36b-4325-8ca0-415098269071
-- title:
--   Simultaneous rational specialization for open quasi-finite affine families
-- statement:
--   Let $K$ be an algebraically closed field, let $A=K[t_\lambda]_{\lambda\in\Lambda}$ with $\Lambda$ finite, and let $I$ be a finite index set. For each $i\in I$, let $R_i$ be a finite-type $A$-algebra, with the compatible $K$-algebra structure. Assume that
--   $$
--   \operatorname{Spec}R_i\longrightarrow\operatorname{Spec}A
--   $$
--   is open and quasi-finite.
--
--   Fix $c_0\in K^\Lambda$ and $K$-algebra homomorphisms $e_{i,0}:R_i\to K$ whose restrictions to $A$ are evaluation at $c_0$. A polynomial $P$ in finitely many labelled elements of the $R_i$, with coefficients in $K$, can be evaluated at any tuple of such homomorphisms. Suppose
--   $$
--   P((e_{i,0}(r))_{(i,r)})\ne0.
--   $$
--   Then there is a Zariski-open neighborhood $U$ of the evaluation ideal $\mathfrak m_{c_0}$ in $\operatorname{Spec}A$ such that, whenever $c\in K^\Lambda$ has $\mathfrak m_c\in U$, there are $K$-algebra homomorphisms $e_i:R_i\to K$ satisfying
--   $$
--   e_i|_A=\operatorname{ev}_c\quad(i\in I),\qquad
--   P((e_i(r))_{(i,r)})\ne0.
--   $$
--   Thus finitely many rational points can be specialized together while retaining any prescribed polynomial nonvanishing condition. This includes empty index sets and empty coefficient-variable sets; nilpotents in the $R_i$ are allowed.
--
--   **Formalization Note.** The variables of $P$ are the disjoint union of the underlying sets of the $R_i$; each polynomial still has finite support. Finite type is stated separately because Mathlib's `Algebra.QuasiFinite` records finite-dimensional residue-field fibers without including finite type. This is an auxiliary algebraic synthesis of universal openness and rational-point existence, not a verbatim numbered source theorem. Its proof remains Open.
--
--   **Verified reduction (8 October 2026).** The finite tensor-product algebra and the rational-point specialization are now proved. The proof constructs the universal evaluation, proves finite generation of the tensor product, and uses its Jacobson property to find maximal ideals avoiding the nonvanishing element. Algebraic closedness produces the required compatible rational homomorphisms. The sole Open input is [openness of finite tensor products over a normal Noetherian domain](https://prove2.me/theorems/12366d22-835f-4ccc-9f99-abe1ff4a5d03). That child contains no rational-point or nonvanishing-polynomial conclusion. The original formal statement is unchanged.
-- source:
--   Stacks Project, Lemma 37.74.2 (Tag 0F32), https://stacks.math.columbia.edu/tag/0F32, universal openness for locally quasi-finite morphisms over a geometrically unibranch locally Noetherian base with dominating components; Theorem 10.34.1 (Tag 00FV), https://stacks.math.columbia.edu/tag/00FV, weak Nullstellensatz for finite-type algebras. Auxiliary consequence: openness forces each irreducible component to dominate the integral polynomial base; pass to the finite fiber product and the principal open of the given polynomial, then take a rational point in each nonempty closed fiber. These transfers remain to be formalized. Philippon application: Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), p.364, the mixed-linear-section paragraph after Lemma 3.1, https://numdam.org/articles/10.24033/bsmf.2060/.

import Mathlib
set_option autoImplicit false
open scoped BigOperators Topology

/-- Simultaneous rational specialization with one nonvanishing constraint. -/
theorem Algebra.exists_open_simultaneous_rational_specialization
    (K : Type*) [Field K] [IsAlgClosed K]
    (σ ι : Type*) [Finite σ] [Finite ι]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)]
    [∀ i, Algebra (MvPolynomial σ K) (R i)]
    [∀ i, IsScalarTower K (MvPolynomial σ K) (R i)]
    [∀ i, Algebra.FiniteType (MvPolynomial σ K) (R i)]
    (hopen : ∀ i, IsOpenMap
      (PrimeSpectrum.comap (algebraMap (MvPolynomial σ K) (R i))))
    (hquasi : ∀ i, Algebra.QuasiFinite (MvPolynomial σ K) (R i))
    (c₀ : σ → K) (e₀ : ∀ i, R i →ₐ[K] K)
    (h₀ : ∀ i (Q : MvPolynomial σ K),
      e₀ i (algebraMap (MvPolynomial σ K) (R i) Q) = MvPolynomial.eval c₀ Q)
    (P : MvPolynomial (Σ i, R i) K)
    (hP : MvPolynomial.eval (fun t => e₀ t.1 t.2) P ≠ 0) :
    ∃ U : Set (PrimeSpectrum (MvPolynomial σ K)), IsOpen U ∧
      MvPolynomial.pointToPoint (k := K) c₀ ∈ U ∧
      ∀ c : σ → K, MvPolynomial.pointToPoint (k := K) c ∈ U →
        ∃ e : ∀ i, R i →ₐ[K] K,
          (∀ i (Q : MvPolynomial σ K),
            e i (algebraMap (MvPolynomial σ K) (R i) Q) = MvPolynomial.eval c Q) ∧
          MvPolynomial.eval (fun t => e t.1 t.2) P ≠ 0 := by sorry
