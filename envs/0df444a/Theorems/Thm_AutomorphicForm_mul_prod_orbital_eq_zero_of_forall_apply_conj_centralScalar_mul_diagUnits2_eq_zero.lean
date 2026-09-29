-- Prove2me | Theorems.Thm_AutomorphicForm_mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero
-- name    : AutomorphicForm.mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/098dcd7f-9781-5829-8826-9f3badf64d05
-- title:
--   Vanishing of the ∞–S orbital window from class vanishing
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}_K$, and let $\nu_{Z_K}$ be a Haar measure on the group $(\mathbb{A}_K)^\times$ of ideles of $K$, the idele group carrying its Borel structure. Let $S$ and $T$ be finite sets of finite places of $K$ with $T$ disjoint from $S$, and let $u \in K^\times$ with $u \neq 1$; write $u_{\mathbb{A}}$ for the image of $u$ under the diagonal embedding $K^\times \to (\mathbb{A}_K)^\times$. The hypothesis `hind` requires that for every finite place $v$ outside $S \cup T$ one has $\mathrm{ord}_v(u_{\mathbb{A}}) = 0$, where [`NumberField.Idele.ord`](def/NumberField_IdeleProductMeasure.html#L13) is minus the logarithm of the $v$-adic valuation of the finite part. For an idele $z$ put $\gamma_z := \mathrm{scalar}(z)\cdot\mathrm{diag}(u_{\mathbb{A}}, 1) \in \mathrm{GL}_2(\mathbb{A}_K)$, where `centralScalar` is the central embedding $(\mathbb{A}_K)^\times \to \mathrm{GL}_2(\mathbb{A}_K)$ and `diagUnits2` forms the diagonal matrix with the indicated unit entries.
--
--   Test function data. Functions $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $f_a$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$, $f_f$ on $\mathrm{GL}_2$ of the finite adeles and, for each finite place $v$, $f_v$ on $\mathrm{GL}_2(K_v)$, all complex valued, are assumed to satisfy `IsUnitFactorization K (S ∪ T) f fa ff fS`: the archimedean factor $f_a$ is of the form $\Phi$ composed with the matrix-entry map for some $\Phi$ smooth on the mixed space and is compactly supported; $f_f$ is locally constant with compact support; $f_v$ is locally constant with compact support for every $v \in S \cup T$; for every $h \in \mathrm{GL}_2$ of the finite adeles all of whose components outside $S \cup T$ lie in the local integral set (the matrices with integral entries whose inverse also has integral entries) one has $f_f(h) = \prod_{v \in S \cup T} f_v(h_v)$, while $f_f(h) = 0$ as soon as some component outside $S \cup T$ fails to lie in that set; and $f(g) = f_a(g_\infty)\, f_f(g_{\mathrm{fin}})$ for all $g$.
--
--   Local central invariance at $T$. The hypothesis `hcen` requires, for each $v \in T$, that $f_v$ be invariant under left translation by every $c \in \mathrm{GL}_2(K_v)$ whose matrix is $\varepsilon \cdot 1$ for some $\varepsilon \in K_v$ with valuation $1$.
--
--   Global vanishing. The hypothesis `hvan` requires $f(x^{-1}\gamma_{z'}x) = 0$ for every idele $z'$ and every $x \in \mathrm{GL}_2(\mathbb{A}_K)$; that is, $f$ vanishes on the whole conjugacy class of $\gamma_{z'}$ for all central twists $z'$.
--
--   Measures and factorisation constants. A real constant $c_{\tau K} > 0$ is given, together with a Haar measure $\nu_A$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ for the Borel structure `glBorelOf`, and a real constant $c_G$ subject to the global Euler factorisation hypothesis `hG`: for every finite set $S'$ of finite places and every triple of functions $(f', f'_a, f'_\bullet)$ such that $f'_a$ is a.e. strongly measurable for $\nu_A$, each $f'_v$ ($v \in S'$) is a.e. strongly measurable for the local Haar measure `localHaar`, $f'(g) = f'_a(g_\infty)\prod_{v \in S'} f'_v(g_v)$ whenever all components of $g$ outside $S'$ lie in the local integral set, and $f'(g) = 0$ whenever some component outside $S'$ fails to, one has $\int f' \, d(\mathrm{adelicGLHaar}) = c_G \left(\int f'_a \, d\nu_A\right)\prod_{v \in S'} \int f'_v \, d(\mathrm{localHaar})$.
--
--   Centralizer measures. For each idele $z$ there are given: a Haar measure $\tau_G(z)$ on the centralizer of $\{\gamma_z\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$, subject to the comparison hypothesis `hτGc` asserting that for every $g : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ the integral of $g$ over that centralizer against $\tau_G(z)$ equals $c_{\tau K} \int g(\mathrm{diag}(p_1,p_2))\, d(\nu_{Z_K} \times \nu_{Z_K})(p)$; a Haar measure $\tau_A(z)$ on the centralizer of the archimedean part of $\gamma_z$, for the Borel structure `centralizerBorel`; and, for each finite place $v$, a Haar measure $\tau_F(z,v)$ on the local centralizer of the $v$-component of $\gamma_z$, for the Borel structure `localCentralizerBorel`, normalised by `hτF1` so that $\tau_F(z,v)$ of the preimage of the local integral set equals $1$. A real constant $c_T > 0$ is given with the centralizer Euler factorisation hypothesis `hT`: for every idele $z$, every finite set $S'$ and all $(W, W_a, W_\bullet)$ satisfying the corresponding a.e. strong measurability conditions with respect to $\tau_A(z)$ and the $\tau_F(z,v)$, the product formula $W(t) = W_a(t_\infty)\prod_{v \in S'} W_v(t_v)$ for elements $t$ of the centralizer of $\gamma_z$ all of whose components outside $S'$ are in the local integral set, and $W(t) = 0$ when some such component is not, one has $\int W \, d\tau_G(z) = c_T \left(\int W_a \, d\tau_A(z)\right)\prod_{v \in S'} \int W_v \, d\tau_F(z,v)$.
--
--   Orbital integral data. A function $I_A$ on ideles is given with, for every $z$, `IsOrbitalIntegralOn` holding for $\nu_A$, the archimedean part of $\gamma_z$, $\tau_A(z)$, $f_a$ and $I_A(z)$: there is a non-negative measurable compactly supported weight $w$ with $\int_{\text{centralizer}} w(tx)\, d\tau_A(z) = 1$ for every $x$ with $f_a(x^{-1}\gamma_{z,\infty}x) \neq 0$, and $I_A(z) = \int f_a(x^{-1}\gamma_{z,\infty}x)\, w(x)\, d\nu_A$. A function $I_F$ of an idele and a finite place is given with, for every $z$ and every $v \in S$, the analogous local statement `IsOrbitalIntegral` for the $v$-component of $\gamma_z$, $\tau_F(z,v)$, $f_v$ and $I_F(z,v)$, the outer integral being against `localHaar`.
--
--   Shell data at $T$. Elements $\varpi_v$ of the valuation ring of $K_v$ are given for all $v$, irreducible for $v \in T$; integers $e_v$; and elements $t_v \in \mathrm{GL}_2(K_v)$ with $t_v = \mathrm{diag}(\varpi_v^{e_v} u,\, \varpi_v^{e_v})$ for $v \in T$, where $u$ is taken in $K_v$ via the structure map. The hypothesis `hshell` requires, for each $v \in T$, the existence of a Haar measure $\tau$ on the local centralizer of $t_v$ giving mass $1$ to the preimage of the local integral set, and of a complex number $I \neq 0$ which is an orbital integral of $f_v$ at $t_v$ with respect to $\tau$ in the sense of `IsOrbitalIntegral`.
--
--   Conclusion: for the given idele $z$,
--   $$I_A(z) \cdot \prod_{v \in S} I_F(z,v) = 0 .$$
--
--   This is the vanishing step in the comparison of adelic orbital contributions attached to the split regular class of $\mathrm{diag}(u,1)$: global vanishing of the test function on all central twists of that class, combined with non-vanishing of the local orbital integrals on the prescribed shells at the places of $T$, forces the product of the archimedean orbital integral with the orbital integrals at the places of $S$ to vanish. It is used in the packaging of trace-formula contributions into slot families, via [`AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted`](thm.html#AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_orbital_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_smul_eq_map_partAt_of_ne_one_unweighted).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.mul_prod_orbital_eq_zero_of_forall_apply_conj_centralScalar_mul_diagUnits2_eq_zero
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (hind : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T →
      NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0)
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (S ∪ T) f fa ff fS)
    (hcen : ∀ v ∈ T, ∀ c : GL (Fin 2) (v.adicCompletion K),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y : GL (Fin 2) (v.adicCompletion K), fS v (c * y) = fS v y)

    (hvan : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      f (x⁻¹ * ((AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) * x) = 0)
    (cτK : ℝ) (hcτK : 0 < cτK)
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hνA : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) νA)
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa νA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (τG : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ z, (τG z).IsHaarMeasure)
    (hτGc : ∀ z, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ z, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA z))
    (τF : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ z v, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF z v))
    (hτF1 : ∀ z v, τF z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (S' : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA z) →
        (∀ v ∈ S', AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S', WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG z) = cT * (∫ t, Wa t ∂(τA z)) * ∏ v ∈ S', ∫ t, WS v t ∂(τF z v))

    (IA : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ z, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA z) fa (IA z))
    (IF : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ z, ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z v) (fS v) (IF z v))

    (ϖT : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) (hϖT : ∀ v ∈ T, Irreducible (ϖT v))
    (eT : HeightOneSpectrum (𝓞 K) → ℤ)
    (tT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (htT : ∀ v ∈ T, (tT v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖT v : v.adicCompletion K) ^ eT v * algebraMap K (v.adicCompletion K) (u : K),
        (ϖT v : v.adicCompletion K) ^ eT v])
    (hshell : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      ∃ (τ : @Measure (AutomorphicForm.localCentralizer K v (tT v)) (AutomorphicForm.localCentralizerBorel K v (tT v)))
        (I : ℂ), @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (tT v)) τ ∧
          τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 ∧
          AutomorphicForm.IsOrbitalIntegral K v (tT v) τ (fS v) I ∧ I ≠ 0)
    (z : (AdeleRing (𝓞 K) K)ˣ) :
    IA z * ∏ v ∈ S, IF z v = 0 := by sorry
