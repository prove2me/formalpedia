-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_symmValue_rows_kernel_iff
-- name    : AlgebraicCurve.Divisor.exists_symmValue_rows_kernel_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/cce30993-7839-5a97-a8be-8062e00efee1
-- title:
--   Riemann–Roch spaces as kernels of a uniform symmetric-value system
-- statement:
--   Let $K_0\subseteq$-valued data be as follows: fields $K_0,k,F$ with $k$ a $K_0$-algebra and $F$ a $k$-algebra, an element $j\in F$ transcendental over $k$ such that $F$ is finite and separable over the intermediate field $k(j)=k(\{j\})$, and $\operatorname{char} k=0$. Here a place of $F/k$ is a valuation subring $v\subseteq F$, not equal to $F$, containing $\operatorname{im}(k\to F)$ and a principal ideal ring; $v.\mathrm{ord}$ is minus the logarithm of the associated adic valuation, a divisor is a finitely supported $\mathbb Z$-valued function on places, and $\deg D=\sum_v D(v)\deg v$. Assume: every nonzero $x\in F$ fails to lie in only finitely many of these valuation subrings ($hfin$); for every place $v$ with $j\in v$ and every $x$ integral over $k[j]$ there is $c\in k$ with $x=c$ or $v.\mathrm{ord}(x-c)>0$ ($hrat$); $b:\mathrm{Fin}\,n\to F$ is $k[j]$-linearly independent ($\sum_i c_i(j)b_i=0$ forces all $c_i=0$) and spans $F$ after clearing a denominator ($\forall x\,\exists q\ne0,c$ with $x\,q(j)=\sum_i c_i(j)b_i$); and the multiplication table of $b$ is defined over $K_0$: $b_ib_{i'}d(j)=\sum_{i''}A_{i,i'',i'}(j)b_{i''}$ with $0\ne d\in K_0[X]$ and $A_{i}\in M_n(K_0[X])$. Fix further $q_0\in K_0[X]$, a place $v_0$, and $g,e,m\in\mathbb N$ (the last written $mdeg$). The conclusion asserts the existence of data independent of the divisor: $\Theta\in K_0[X]$; an $a\in\mathbb N$ with polynomials $cL_0(s)$, $cL(s,i)\in K_0[X]$ defining the elements $L_s=cL_0(s)(j)+\sum_i cL(s,i)(j)\,b_i$, and $\chi_s\in K_0[X][Y]$; an $M\in\mathbb N$ with, for each $l<M$, a rectangular matrix $Y_l$ of size $Rm(l)\times(n\cdot(m+1))$ over $k$ (columns indexed by pairs $(i,dd)$ with $i<n$, $dd\le m$); and, for each $r\le g$, an $R(r)$-indexed family of column vectors $P(r,\rho,\mathrm{col})$ of polynomials in the variables $\mathrm{Fin}(a+1)\times\mathrm{Fin}(r+1)$ over $K_0$; such that each $\chi_s$ is monic (in $Y$ over $K_0[X]$), and for every effective divisor $D$ (all $D(v)\ge0$) of degree $g$ there are $r\le g$, an index $l<M$, places $pt_t$ ($t<r$) and $pt'_{t'}$ ($t'<r'$ for some $r'$), values $\mathrm{val}(t,s)\in k$ for $s\le a$, and $jv'_{t'}\in k$, with: $v.\mathrm{ord}\,j\ge0$ and $v.\mathrm{ord}\,\Theta(j)=0$ at each $v=pt_t$; $v.\mathrm{ord}\,\Theta(j)>0$ at each $v=pt'_{t'}$; $D$ agrees, at every place where $j$ is regular, with $\sum_t [pt_t]+\sum_{t'}[pt'_{t'}]$; $pt_t.\mathrm{ord}(j-\mathrm{val}(t,0))>0$ and $pt_t.\mathrm{ord}(L_s-\mathrm{val}(t,s+1))>0$ for all $s<a$; $pt'_{t'}.\mathrm{ord}(j-jv'_{t'})>0$; $\chi_s$ vanishes at $(\mathrm{val}(t,0),\mathrm{val}(t,s+1))$ for all $t,s$; and finally, for every $u:\mathrm{Fin}\,n\times\mathrm{Fin}(m+1)\to k$, the simultaneous vanishing of the linear forms $\sum_{\mathrm{col}}P(r,\rho,\mathrm{col})\big(\text{coefficients of }\prod_{t<r}(X-\mathrm{val}(t,s))\big)\,u_{\mathrm{col}}$ (for $\rho<R(r)$, the variable indexed $(s,\kappa)$ being specialised to the $\kappa$-th coefficient of that monic polynomial, i.e. to the elementary symmetric functions of the values $\mathrm{val}(\cdot,s)$) together with $\sum_{\mathrm{col}}Y_l(\rho,\mathrm{col})u_{\mathrm{col}}=0$ (for $\rho<Rm(l)$) is equivalent to: $u=0$, or for every place $v$, $\;(D-e\,[v_0])(v)+v.\mathrm{ord}\big(f_u\cdot h^{-1}\big)\ge0$, where $f_u=\sum_i\big(\sum_{dd}u(i,dd)X^{dd}\big)(j)\,b_i$ and $h=\big(\prod_{t<r}(X-\mathrm{val}(t,0))\prod_{t'}(X-jv'_{t'})\,q_0\big)(j)$.
--
--   The statement packages the Riemann–Roch spaces $L(D-e\,[v_0])$, for $D$ running over all effective divisors of degree $g$ on the curve with function field $F/k$, as the kernels of linear systems drawn from a finite list fixed in advance, whose coefficients are universal polynomials over $K_0$ evaluated at the elementary symmetric functions of the coordinates $\mathrm{val}(t,s)$ of the points of $D$ — so that the system depends on $D$ only through those symmetric values. It is used in the construction of a height system on the modular function field, via [`ModularCurve.exists_height_system_modularFunctionFieldBar`](thm.html#ModularCurve.exists_height_system_modularFunctionFieldBar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_symmValue_rows_kernel_iff.lean

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Algebra.MvPolynomial.Eval

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.Divisor.exists_symmValue_rows_kernel_iff
    {K₀ k F : Type*} [Field K₀] [Field k] [Field F] [Algebra K₀ k] [Algebra k F]
    {j : F} (hj : Transcendental k j)
    [FiniteDimensional (IntermediateField.adjoin k ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin k ({j} : Set F)) F] [CharZero k]
    (hfin : ∀ x : F, x ≠ 0 → {v : Place k F | x ∉ v.toValuationSubring}.Finite)
    (hrat : ∀ (v : Place k F) (x : F), j ∈ v.toValuationSubring →
      IsIntegral (Algebra.adjoin k ({j} : Set F)) x →
      ∃ c : k, x = algebraMap k F c ∨ 0 < v.ord (x - algebraMap k F c))
    (n : ℕ) (b : Fin n → F)
    (hbli : ∀ c : Fin n → Polynomial k,
      (∑ i : Fin n, Polynomial.aeval j (c i) * b i) = 0 → ∀ i, c i = 0)
    (hbsp : ∀ x : F, ∃ (q : Polynomial k) (c : Fin n → Polynomial k), q ≠ 0 ∧
      x * Polynomial.aeval j q = ∑ i : Fin n, Polynomial.aeval j (c i) * b i)
    (d : Polynomial K₀) (hd : d ≠ 0) (A : Fin n → Matrix (Fin n) (Fin n) (Polynomial K₀))
    (hmul : ∀ i i' : Fin n, b i * b i' * Polynomial.aeval j (d.map (algebraMap K₀ k))
      = ∑ i'' : Fin n, Polynomial.aeval j ((A i i'' i').map (algebraMap K₀ k)) * b i'')
    (q₀ : Polynomial K₀) (v₀ : Place k F) (g e mdeg : ℕ) :
    ∃ (Θ : Polynomial K₀) (a : ℕ) (cL₀ : Fin a → Polynomial K₀) (cL : Fin a → Fin n → Polynomial K₀)
      (χ : Fin a → Polynomial (Polynomial K₀))
      (M : ℕ) (Rm : Fin M → ℕ) (Y : (l : Fin M) → Fin (Rm l) → Fin n × Fin (mdeg + 1) → k)
      (R : Fin (g + 1) → ℕ)
      (P : (r : Fin (g + 1)) → Fin (R r) → Fin n × Fin (mdeg + 1) →
        MvPolynomial (Fin (a + 1) × Fin ((r : ℕ) + 1)) K₀),
      (∀ s, (χ s).Monic) ∧
      ∀ (D : Divisor k F), (∀ v, 0 ≤ D v) → Divisor.degree D = (g : ℤ) →
        ∃ (r : Fin (g + 1)) (l : Fin M) (pt : Fin (r : ℕ) → Place k F)
          (val : Fin (r : ℕ) × Fin (a + 1) → k)
          (r' : ℕ) (pt' : Fin r' → Place k F) (jv' : Fin r' → k),
          (∀ t, 0 ≤ (pt t).ord j ∧
            (pt t).ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k))) = 0) ∧
          (∀ t', 0 < (pt' t').ord (Polynomial.aeval j (Θ.map (algebraMap K₀ k)))) ∧
          (∀ v : Place k F, 0 ≤ v.ord j → D v =
            ((∑ t, Finsupp.single (pt t) (1 : ℤ))
              + ∑ t', Finsupp.single (pt' t') (1 : ℤ) : Divisor k F) v) ∧
          (∀ t, 0 < (pt t).ord (j - algebraMap k F (val (t, 0)))) ∧
          (∀ t (s : Fin a), 0 < (pt t).ord
            ((Polynomial.aeval j ((cL₀ s).map (algebraMap K₀ k))
              + ∑ i : Fin n, Polynomial.aeval j ((cL s i).map (algebraMap K₀ k)) * b i)
              - algebraMap k F (val (t, s.succ)))) ∧
          (∀ t', 0 < (pt' t').ord (j - algebraMap k F (jv' t'))) ∧
          (∀ t (s : Fin a), Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K₀ k) (val (t, 0)))
              (val (t, s.succ)) (χ s) = 0) ∧
          ∀ u : Fin n × Fin (mdeg + 1) → k,
            ((∀ ρ : Fin (R r), ∑ col, MvPolynomial.aeval
                  (fun ak : Fin (a + 1) × Fin ((r : ℕ) + 1) =>
                    (∏ t : Fin (r : ℕ), (Polynomial.X - Polynomial.C (val (t, ak.1)))).coeff ak.2)
                  (P r ρ col) * u col = 0) ∧
              (∀ ρ : Fin (Rm l), ∑ col, Y l ρ col * u col = 0)) ↔
            (u = 0 ∨ ∀ v : Place k F,
              0 ≤ (D - (e : ℤ) • Finsupp.single v₀ 1 : Divisor k F) v
                + v.ord ((∑ i : Fin n, Polynomial.aeval j
                      (∑ dd : Fin (mdeg + 1), Polynomial.C (u (i, dd)) * Polynomial.X ^ (dd : ℕ)) * b i)
                    * (Polynomial.aeval j
                        ((∏ t : Fin (r : ℕ), (Polynomial.X - Polynomial.C (val (t, 0))))
                          * (∏ t', (Polynomial.X - Polynomial.C (jv' t')))
                          * q₀.map (algebraMap K₀ k)))⁻¹)) := by sorry
