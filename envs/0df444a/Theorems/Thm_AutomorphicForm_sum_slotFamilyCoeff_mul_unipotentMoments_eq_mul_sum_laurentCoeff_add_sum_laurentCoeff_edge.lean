-- Prove2me | Theorems.Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge
-- name    : AutomorphicForm.sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/244fbdbd-f85c-5869-839d-080cabce7b3a
-- title:
--   Slot-family assembly of the explicit unipotent moments
-- statement:
--   Data: two number fields $K$ and $L$ with $L$ a $K$-algebra; a family `ws` assigning to every height-one prime $v$ of $\mathcal{O}_K$ an extension $w_v$ of $v$ to $\mathcal{O}_L$ (an element of `v.Extension (𝓞 L)`, i.e. a height-one prime of $\mathcal{O}_L$ whose restriction to $\mathcal{O}_K$ is $v$); a finite set $T$ of height-one primes of $\mathcal{O}_K$; an arbitrary map $w'$ from height-one primes of $\mathcal{O}_K$ to height-one primes of $\mathcal{O}_L$; homomorphisms $\xi_K$ and $\xi_L$ from the full subgroup $\top$ of the unit groups of the adele rings of $K$, resp. $L$, to $\mathbb{C}^\times$; and two functions $\sigma r$ and $s$ from height-one primes of $\mathcal{O}_K$ to $\mathbb{C}$.
--
--   Write $N(\cdot)$ for the absolute norm of an ideal, $f_v :=$ `SatakeCombination.slotDeg K L ws v`, which is the inertia degree `v.asIdeal.inertiaDeg' (ws v).1.asIdeal` of $w_v$ over $v$, and, for a height-one prime $v$ of $\mathcal{O}_K$,
--   $$\xi_v := \xi_K\big(\det \mathrm{heckeGen}(\mathcal{O}_K,K,v)\big) \in \mathbb{C},$$
--   where `heckeGen (𝓞 K) K v` is the element of $GL_2(\mathbb{A}_K)$ obtained from the uniformiser unit at $v$ in the local completion by the inclusion of local units into adelic units followed by `diagOne`, and $\det$ is the `GeneralLinearGroup.det` of that element, taken in $\top$; similarly $\zeta_v := \xi_L\big(\det \mathrm{heckeGen}(\mathcal{O}_L,L,w'_v)\big)$.
--
--   Four families of hypotheses, each imposed for every $v \in T$ only, are assumed: `hσ`, that $\sigma r_v^{\,2} = N(v)\,\xi_v$ (the factor $N(v)$ being `HeckeEigensystem.cNorm v`, the absolute norm of $v$ read in $\mathbb{C}$); `hs`, that $\sqrt{N(w'_v)}\,s_v = \sigma r_v^{\,f_v}$, the square root being taken in $\mathbb{R}$ and then coerced; `hζ`, that $\xi_v^{\,f_v} = \zeta_v$; and `hNws`, that $N(w_v) = N(v)^{f_v}$ as natural numbers.
--
--   Further data: two functions $k$ and $j$ from height-one primes of $\mathcal{O}_K$ to $\mathbb{N}$, complex scalars $\Lambda$ and $\kappa_0$, two weight functions $c_1, c_2$ from height-one primes of $\mathcal{O}_K$ to $\mathbb{C}$, and a real number $R$.
--
--   For $v \in T$ and an exponent vector $r \colon \mathrm{Fin}\,2 \to_0 \mathbb{N}$ put
--   $$A_v(r) = \tfrac{1+(-1)^{r_0}}{2}\,\big(4\,N(v)\,\xi_v\big)^{\lfloor r_0/2\rfloor}\Big(\prod_{n<\lfloor r_0/2\rfloor}\tfrac{2n+1}{2n+2}\Big)\,\xi_v^{\,r_1},\qquad B_v(r) = \big(1+(-1)^{r_0}\big)\big(4\,N(v)\,\xi_v\big)^{\lfloor r_0/2\rfloor}\xi_v^{\,r_1},$$
--   the divisions $r_0/2$ being natural-number division and the displayed product being formed in $\mathbb{R}$ and coerced to $\mathbb{C}$.
--
--   The left-hand side of the asserted identity is the sum over $m \in$ `SatakeCombination.slotIndex K L ws k j T`, that is over all dependent functions assigning to each $v \in T$ (together with its membership proof) an exponent vector in the support of the two-variable polynomial `SatakeCombination.slotWord K L ws v (k v) (j v)` $=$ `univWord (f_v - 1) (k v) (j v)`, of
--   $$\mathrm{slotFamilyCoeff}(m)\cdot\Big[\Lambda\Big(R\prod_{i\in T}A_i(m_i) + \sum_{p\in T}\big(c_1(p)B_p(m_p)+c_2(p)A_p(m_p)\big)\prod_{i\in T,\ i\neq p}A_i(m_i)\Big) + \kappa_0\prod_{i\in T}A_i(m_i)\Big],$$
--   where $m_i$ denotes the value of $m$ at $i$ and `SatakeCombination.slotFamilyCoeff K L ws k j T m` is the product over $v \in T$ of `slotCoeff K L ws v (k v) (j v) (m v)`, the latter being the coefficient of the slot word at $m_v$ times $N(v)^{(m_v)_1}$ divided by $N(w_v)^{j_v}$.
--
--   To describe the right-hand side, let $\iota :=$ `T.equivFin` be the enumeration $T \simeq \mathrm{Fin}\,|T|$ and $v_i := \iota^{-1}(i)$. For an integer vector $n$ indexed by $\mathrm{Fin}\,|T|$ put
--   $$\hat G(n) = \prod_{i}\big(\sqrt{N(w'_{v_i})}\,s_{v_i}\big)^{k_{v_i}}\,\zeta_{v_i}^{\,j_{v_i}}\,\big[(T^{1}+T^{-1})^{k_{v_i}}\big]_{n_i},$$
--   the last factor being the coefficient of the Laurent polynomial $(T^1+T^{-1})^{k_{v_i}}$ over $\mathbb{C}$ at $n_i$, and let all sums in $n$ range over the box `Fintype.piFinset` of vectors with $n_i \in [-k_{v_i}, k_{v_i}]$. Write
--   $$S_0 = \sum_{n}\hat G(n)\prod_i\big(\text{$1$ if $n_i=0$, else $0$}\big),\qquad S_p^{\flat} = \sum_{n}\hat G(n)\Big(\prod_{i\neq \iota(p)}\big(\text{$1$ if $n_i=0$, else $0$}\big)\Big)\big(1+(-1)^{f_p\,|n_{\iota(p)}|}\big)$$
--   for $p \in T$, where $|\cdot|$ is the natural absolute value of an integer.
--
--   The conclusion is the single equation stating that the above sum over the slot family equals
--   $$R\,\big(\Lambda\,S_0\big) + \Big(\Lambda\sum_{p\in T}\big(c_1(p)\,S_p^{\flat} + c_2(p)\,S_0\big) + \kappa_0\,S_0\Big).$$
--
--   This is the assembly step of the Satake-combination computation: it converts the place-by-place closed forms of the explicit unipotent moment expressions over $K$, summed against the slot-family coefficients of the word $(k,j)$ along $T$, into the Laurent-coefficient array over $L$ of that word, with one distinguished place carrying the edge moment. It is obtained from the two single-place identities [`AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero`](thm.html#AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentMoment_eq_mul_laurentCoeff_zero) and [`AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge`](thm.html#AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_unipotentEdgeMoment_eq_mul_sum_laurentCoeff_edge), and is used by [`AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add`](thm.html#AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge.lean

import Mathlib
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.sum_slotFamilyCoeff_mul_unipotentMoments_eq_mul_sum_laurentCoeff_add_sum_laurentCoeff_edge
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (σr s : HeightOneSpectrum (𝓞 K) → ℂ)
    (hσ : ∀ v ∈ T, σr v ^ 2 = HeckeEigensystem.cNorm v *
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hs : ∀ v ∈ T, ((Real.sqrt (Ideal.absNorm (w' v).asIdeal : ℝ) : ℂ) * s v) =
      σr v ^ SatakeCombination.slotDeg K L ws v)
    (hζ : ∀ v ∈ T,
      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^
          SatakeCombination.slotDeg K L ws v =
        ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hNws : ∀ v ∈ T, Ideal.absNorm (ws v).1.asIdeal =
      Ideal.absNorm v.asIdeal ^ SatakeCombination.slotDeg K L ws v)
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ) (Λ κ₀ : ℂ) (c₁ c₂ : HeightOneSpectrum (𝓞 K) → ℂ) (R : ℝ) :
    ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
      SatakeCombination.slotFamilyCoeff K L ws ks js T m *
        (Λ * ((R : ℂ) *
                ∏ i : T,
                  ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                      ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                          Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                    ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1) +
                ∑ p : T,
                  (c₁ p.1 *
                      ((1 + (-1 : ℂ) ^ (m p.1 p.2) 0) * (4 * (HeckeEigensystem.cNorm p.1 *
                          ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                              Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m p.1 p.2) 0 / 2) *
                        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m p.1 p.2) 1) +
                      c₂ p.1 *
                      ((1 + (-1 : ℂ) ^ (m p.1 p.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm p.1 *
                          ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                              Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m p.1 p.2) 0 / 2) *
                        ((∏ n ∈ Finset.range ((m p.1 p.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m p.1 p.2) 1)) *
                    ∏ i ∈ Finset.univ.erase p,
                      ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                          ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                              Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                        ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                        ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                            Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1)) +
              κ₀ * ∏ i : T,
                ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                  ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                  ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                      Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1)) =
      (R : ℂ) * (Λ *
          ∑ n ∈ Fintype.piFinset
            (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
          (∏ i : Fin T.card,
            ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
            ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
            ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
              LaurentPolynomial ℂ).coeff (n i)) *
          (∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0))) +
        (Λ * ∑ p : T,
            (c₁ p.1 *
              ∑ n ∈ Fintype.piFinset
                (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
              (∏ i : Fin T.card,
                ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                    s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                  LaurentPolynomial ℂ).coeff (n i)) *
              ((∏ i ∈ Finset.univ.erase (T.equivFin p), (if n i = 0 then (1 : ℂ) else 0)) *
                (1 + (-1 : ℂ) ^ (SatakeCombination.slotDeg K L ws p.1 * (n (T.equivFin p)).natAbs))) +
             c₂ p.1 *
              ∑ n ∈ Fintype.piFinset
                (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
              (∏ i : Fin T.card,
                ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                    s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
                ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                  LaurentPolynomial ℂ).coeff (n i)) *
              (∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0))) +
          κ₀ *
            ∑ n ∈ Fintype.piFinset
              (fun i : Fin T.card => Finset.Icc (-(ks (T.equivFin.symm i).1 : ℤ)) (ks (T.equivFin.symm i).1)),
            (∏ i : Fin T.card,
              ((Real.sqrt (Ideal.absNorm (w' (T.equivFin.symm i).1).asIdeal : ℝ) : ℂ) *
                  s (T.equivFin.symm i).1) ^ ks (T.equivFin.symm i).1 *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' (T.equivFin.symm i).1)),
                  Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js (T.equivFin.symm i).1 *
              ((LaurentPolynomial.T 1 + LaurentPolynomial.T (-1)) ^ ks (T.equivFin.symm i).1 :
                LaurentPolynomial ℂ).coeff (n i)) *
            (∏ i : Fin T.card, (if n i = 0 then (1 : ℂ) else 0))) := by sorry
