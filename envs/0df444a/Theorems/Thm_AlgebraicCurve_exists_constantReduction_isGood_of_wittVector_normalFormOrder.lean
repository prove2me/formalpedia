-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_constantReduction_isGood_of_wittVector_normalFormOrder
-- name    : AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/08c2567f-1c71-54f5-9243-1c181580ed77
-- title:
--   Good constant reduction of a normal-form Witt lift
-- statement:
--   Fix a prime $p$ and an algebraically closed field $K$ of characteristic $p$, and let $W = \mathrm{WittVector}\ p\ K$. Let $n$ be a natural number and $Bt$ a commutative $W[X]$-algebra admitting a $W[X]$-basis $bt$ indexed by $\mathrm{Fin}(n+1)$, together with weights $d : \mathrm{Fin}(n+1) \to \mathbb{N}$, such that $bt\,0 = 1$, $d\,0 = 0$, $d\,i \in \{1,2\}$ for $i \neq 0$, and the structure constants are in normal form: for $i, j \neq 0$ and every $k$, the $k$-th coordinate of $bt\,i \cdot bt\,j$ in the basis has natural degree at most $d\,i + d\,j - d\,k$ (truncated subtraction). Let $F$ be a field which is a $K$-algebra and $\psi : Bt \to F$ a ring homomorphism such that $\psi$ sends the constant polynomial $C\,a$, $a \in W$, to the image in $F$ of the zeroth Witt coordinate $a.\mathrm{coeff}\,0 \in K$; such that, writing $\bar x = \psi(X)$, the elements $\psi(bt\,i)$ are linearly independent over the polynomials in $\bar x$, i.e. $\sum_i \mathrm{aeval}_{\bar x}(c\,i)\,\psi(bt\,i) = 0$ with $c : \mathrm{Fin}(n+1) \to K[X]$ forces $c = 0$; and such that every $z \in F$ is a fraction, $z\,\psi(h) = \psi(f)$ with $\psi(h) \neq 0$. Assume finally $\mathrm{genusFF}\,K\,F + n = \sum_i d\,i$, where $\mathrm{genusFF}$ is the $K$-dimension of $H^1$ of the zero divisor. The conclusion asserts the existence of an algebraically closed field $L$ of characteristic $0$, a valuation subring $A \subseteq L$, a ring isomorphism $e$ from the residue field of $A$ onto $K$, a field $F'$ that is an $L$-algebra, and an algebra structure of the residue field of $A$ on $F$, such that: the structure map from the residue field of $A$ to $F$ is $e$ followed by the structure map $K \to F$; there is $x \in F'$ transcendental over $L$ with $F'$ finite-dimensional over $L(x)$; and there is a constant reduction $R$ of $F'$ along $A$ with residue field $F$ which is good. Here a constant reduction consists of a valuation subring $\mathcal{O}$ of $F'$, a surjective ring homomorphism $\mathrm{res} : \mathcal{O} \to F$ with kernel the maximal ideal of $\mathcal{O}$, and a map on places $\mathrm{Place}\,L\,F' \to \mathrm{Place}(A/\mathfrak{m}_A)\,F$, subject to: $\mathcal{O}$ meets $L$ exactly in $A$, $\mathrm{res}$ restricted to $A$ is the residue map of $A$, every nonzero $f \in F'$ has an $L$-multiple lying in $\mathcal{O}$ with nonzero residue, the map on places preserves degrees, and pushing forward the divisor of a function with nonzero residue gives the divisor of its residue; goodness means $\mathrm{genusFF}(A/\mathfrak{m}_A)\,F = \mathrm{genusFF}\,L\,F'$.
--
--   This is the lifting half of Deuring's theory of constant reduction: a function field of one variable over an algebraically closed field of characteristic $p$, presented by a normal-form basis over $K[\bar x]$ whose weights are extremal for the genus, is realised as the good constant reduction of a characteristic-zero function field obtained by passing to Witt vectors. It feeds into [`AlgebraicCurve.exists_charZero_constantReduction_isGood`](thm.html#AlgebraicCurve.exists_charZero_constantReduction_isGood), which removes the normal-form presentation from the hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_constantReduction_isGood_of_wittVector_normalFormOrder.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

universe u v

theorem AlgebraicCurve.exists_constantReduction_isGood_of_wittVector_normalFormOrder
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [IsAlgClosed K] [CharP K p]
    (n : ℕ) (Bt : Type u) [CommRing Bt] [Algebra (WittVector p K)[X] Bt]
    (bt : Module.Basis (Fin (n + 1)) (WittVector p K)[X] Bt) (d : Fin (n + 1) → ℕ)
    (hbt0 : bt 0 = 1) (hd0 : d 0 = 0) (hd : ∀ i, i ≠ 0 → d i = 1 ∨ d i = 2)
    (hdeg : ∀ i j k, i ≠ 0 → j ≠ 0 → ((bt.repr (bt i * bt j)) k).natDegree ≤ d i + d j - d k)
    (F : Type v) [Field F] [Algebra K F] (ψ : Bt →+* F)
    (hψC : ∀ a : WittVector p K,
      ψ (algebraMap (WittVector p K)[X] Bt (Polynomial.C a)) = algebraMap K F (a.coeff 0))
    (hψind : ∀ c : Fin (n + 1) → K[X],
      ∑ i, Polynomial.aeval (ψ (algebraMap (WittVector p K)[X] Bt Polynomial.X)) (c i) *
        ψ (bt i) = 0 → c = 0)
    (hψfrac : ∀ z : F, ∃ f h : Bt, ψ h ≠ 0 ∧ z * ψ h = ψ f)
    (hgen : genusFF K F + n = ∑ i, d i) :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L) (A : ValuationSubring L)
      (e : IsLocalRing.ResidueField A ≃+* K)
      (F' : Type u) (_ : Field F') (_ : Algebra L F') (_ : Algebra (IsLocalRing.ResidueField A) F),
      algebraMap (IsLocalRing.ResidueField A) F = (algebraMap K F).comp e.toRingHom ∧
        (∃ x : F', Transcendental L x ∧
          FiniteDimensional (IntermediateField.adjoin L ({x} : Set F')) F') ∧
        ∃ R : ConstantReduction A F' F, R.IsGood := by sorry
