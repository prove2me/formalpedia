-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6dc489dd-dc92-5806-8f49-09845e02789b
-- title:
--   Archimedean discrepancy window for cyclic base change
-- statement:
--   Setting. Let $K$ and $L$ be number fields with $L/K$ finite Galois, let $\sigma \in \mathrm{Gal}(L/K)$, and assume (`hgen`) that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ and (`hdeg`) that $[L:K] = \mathrm{finrank}_K L$ is prime. Write $K_\infty$ and $L_\infty$ for the infinite adele rings of $K$ and $L$, and $\iota$ for the ring isomorphism `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` from $K_\infty$ to the mixed space of $K$.
--
--   Test factors. Let $\varphi_\infty : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ and $f_\infty : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ satisfy `IsArchTestFactor`: each is compactly supported and is obtained from a function on the space of $2\times 2$ matrices over the corresponding mixed space that is $C^\infty$ over $\mathbb{R}$, evaluated on the mixed-space entries of the argument (`archEntries`). The hypothesis `hmatch` is `AreMatchingArch K L σ φa fa`, i.e. `AreMatchingOn` for the pair $(\varphi_\infty \circ \mathrm{archIdentGL}, f_\infty)$ with respect to the Haar measures `archHaarL K L` on $\mathrm{GL}_2(L \otimes_K K_\infty)$ and `archHaarK K` on $\mathrm{GL}_2(K_\infty)$; it has two clauses: for every $\delta$ whose norm string $\delta\,\sigma(\delta)\cdots\sigma^{[L:K]-1}(\delta)$ is regular semisimple (meaning $\mathrm{tr}^2 - 4\det$ is a unit), every regular semisimple $\gamma$, every $y$ conjugating the norm string of $\delta$ to the image of $\gamma$ under `toTensorGL`, and every pair of Haar measures on the centraliser of $\gamma$ and on the $\sigma$-twisted centraliser of $\delta$ that are coupled through $y$, the twisted orbital integral of $\varphi_\infty \circ \mathrm{archIdentGL}$ at $\delta$ equals the orbital integral of $f_\infty$ at $\gamma$; and for every regular semisimple $\gamma$ which is not a norm, every orbital integral of $f_\infty$ at $\gamma$ vanishes.
--
--   Finally, let $\tau_0$ be a measure on $K_\infty \times K_\infty$, fixed once and for all.
--
--   Conclusion. There exist a function $B$ and families $C = (C_w)_w$, $E = (E_w)_w$ indexed by the infinite places $w$ of $K$, all from $(\mathrm{Fin}\,2) \to \text{mixedSpace}\,K$ to $\mathbb{C}$, with the following properties.
--
--   (i) $B$, each $C_w$ and each $E_w$ are $C^\infty$ over $\mathbb{R}$ and have compact support.
--
--   (ii) For every point $p$ with $B(p) \neq 0$, or with $C_w(p) \neq 0$ or $E_w(p) \neq 0$ for some $w$, both $\iota^{-1}(p\,0)$ and $\iota^{-1}(p\,1)$ are units of $K_\infty$.
--
--   (iii) There is a compact set $C_a \subseteq K_\infty^\times \times K_\infty^\times$ such that every $p$ in $\mathrm{tsupport}\,B \cup \bigcup_w (\mathrm{tsupport}\,C_w \cup \mathrm{tsupport}\,E_w)$ is of the form $p = (\iota(q_1), \iota(q_2))$, viewed as a function on $\mathrm{Fin}\,2$, for some $q = (q_1,q_2) \in C_a$.
--
--   (iv) For all units $a, t$ of $K_\infty$ such that $\gamma = \mathrm{diagUnits2}\,a\,(at) = \mathrm{diag}(a, at)$ is regular semisimple; for every Haar measure $\tau$ on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_\infty)$ whose image under the map $x \mapsto (x_{00}, x_{11})$ is $\tau_0$; and for every $J \in \mathbb{C}$ which is a weighted orbital integral of $f_\infty$ at $\gamma$ with respect to `archHaarK K` and $\tau$, for the weight
--   $$x \mapsto \sum_{w \mid \infty} m_w \log\!\left( \frac{\mathrm{topNormSq}(x_w)\,\mathrm{rowNormSq}(x_w)}{\lVert \det x_w \rVert^2} \right),$$
--   where $x_w$ denotes the matrix of the component of $x$ at $w$ (`archComponent`), $m_w = w.\mathrm{mult}$, $\mathrm{topNormSq}(g) = \lVert g_{00}\rVert^2 + \lVert g_{01}\rVert^2$ and $\mathrm{rowNormSq}(g) = \lVert g_{10}\rVert^2 + \lVert g_{11}\rVert^2$ — being a weighted orbital integral meaning that there is a section function $s$ for $(\gamma, \tau, f_\infty)$ (non-negative, measurable, compactly supported, with $\int_{Z(\gamma)} s(ux)\,d\tau(u) = 1$ whenever $f_\infty(x^{-1}\gamma x) \neq 0$) with $J = \int f_\infty(x^{-1}\gamma x)\,\mathrm{wt}(x)\,s(x)\,d(\text{archHaarK}\,K)(x)$ — the following two assertions hold.
--
--   (iv.a) For all units $\alpha, \beta$ of $L \otimes_K K_\infty$ such that the norm string of $\mathrm{diag}(\alpha,\beta)$ equals the image of $\gamma$ under `toTensorGL`, for every Haar measure $\tau'$ on the $\sigma$-twisted centraliser of $\mathrm{diag}(\alpha,\beta)$ (the subgroup of $u$ with $u\,\delta\,\sigma(u)^{-1} = \delta$) such that $\tau$ and $\tau'$ are coupled with conjugator $1$, that is, the image of $\tau'$ under the inclusion of the twisted centraliser equals the image of $\tau$ under `toTensorGL`, and for every $J' \in \mathbb{C}$ which is a twisted weighted orbital integral of $\varphi_\infty \circ \mathrm{archIdentGL}$ at $\mathrm{diag}(\alpha,\beta)$ with respect to `archHaarL K L` and $\tau'$, for the analogous weight over the infinite places $w$ of $L$ formed from $\mathrm{topNormSq}$, $\mathrm{rowNormSq}$ and $\lVert\det\rVert^2$ of the component at $w$ of $\mathrm{archIdentGL}(x)$ (being such an integral meaning that there is a twisted section function $s$ for $(\mathrm{diag}(\alpha,\beta), \tau', \varphi_\infty \circ \mathrm{archIdentGL})$, with $J' = \int \varphi_\infty(\mathrm{archIdentGL}(x^{-1}\,\mathrm{diag}(\alpha,\beta)\,\sigma(x)))\,\mathrm{wt}(x)\,s(x)\,d(\text{archHaarL}\,K\,L)(x)$), one has
--   $$\left( \prod_{w \mid \infty} \left( \frac{\lVert (1-t)_w \rVert}{\sqrt{\lVert t_w \rVert}} \right)^{m_w} \right) \bigl( J' - [L:K]\,J \bigr) = B(\iota t, \iota a) + \sum_{w \text{ real}} \lVert (1-t)_w \rVert\, C_w(\iota t, \iota a) + \sum_{w \text{ complex}} \lVert (1-t)_w \rVert^2 \log \lVert (1-t)_w \rVert\, E_w(\iota t, \iota a),$$
--   where $x_w = \mathrm{archEval}\,K\,w\,(x)$ is the component at $w$, the sums run over the infinite places of $K$ that are real, respectively complex, and the argument of $B$, $C_w$, $E_w$ is the pair $(\iota t, \iota a)$ in this order.
--
--   (iv.b) If there is no $\delta$ in $\mathrm{GL}_2(L \otimes_K K_\infty)$ of which $\gamma$ is a norm, i.e. no $\delta$ and $y$ with $\mathrm{toTensorGL}(\gamma) = y^{-1}\,(\text{norm string of } \delta)\,y$, then the same identity holds with $J'$ replaced by $0$:
--   $$\left( \prod_{w \mid \infty} \left( \frac{\lVert (1-t)_w \rVert}{\sqrt{\lVert t_w \rVert}} \right)^{m_w} \right) \bigl( 0 - [L:K]\,J \bigr)$$
--   equals the same right-hand side $B(\iota t, \iota a) + \sum_{w \text{ real}} \lVert (1-t)_w \rVert\,C_w(\iota t, \iota a) + \sum_{w \text{ complex}} \lVert (1-t)_w \rVert^2 \log \lVert (1-t)_w \rVert\,E_w(\iota t, \iota a)$.
--
--   The functions $B$, $C_w$, $E_w$ and the compact set $C_a$ are chosen uniformly in $(a,t)$ and in the admissible data $(\tau, \tau', J, J')$, the normalisation of $\tau$ being pinned by $\tau_0$ once for all classes.
--
--   This is the archimedean discrepancy window for cyclic base change in prime degree: along the split regular classes $\mathrm{diag}(a,at)$ of $\mathrm{GL}_2(K_\infty)$, the difference between the twisted weighted orbital integral of the $L$-side test factor and $[L:K]$ times the weighted orbital integral of the matching $K$-side test factor is expressed, after multiplication by the archimedean discriminant factor, as a smooth compactly supported function of $(t,a)$ plus explicit real and complex place corrections. It globalises in $(a,t)$ the corresponding local statement near $t=1$, and is used in the archimedean part of the comparison of the two trace formulae, being cited by [`AutomorphicForm.exists_contDiff_hasCompactSupport_forall_prod_norm_sub_one_pow_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_archDisc_of_areMatchingArch`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_forall_prod_norm_sub_one_pow_mul_twistedWeighted_sub_finrank_mul_weighted_eq_mul_archDisc_of_areMatchingArch) and by [`AutomorphicForm.exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted`](thm.html#AutomorphicForm.exists_forall_window_classSum_eq_tsum_mul_tsum_ite_kinkWindow_of_areMatchingArch_of_areMatchingLocal_of_ne_one_unweighted).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_archDisc_mul_twistedWeighted_sub_finrank_mul_weighted_eq_add_sum_real_add_sum_complex_of_isCompact
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (hmatch : AutomorphicForm.AreMatchingArch K L σ φa fa)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (τ₀ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K)) :
    ∃ (B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ)
      (C E : NumberField.InfinitePlace K → (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) B ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (C w)) ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (E w)) ∧
      HasCompactSupport B ∧ (∀ w, HasCompactSupport (C w)) ∧ (∀ w, HasCompactSupport (E w)) ∧
      (∀ p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K, (B p ≠ 0 ∨ ∃ w, C w p ≠ 0 ∨ E w p ≠ 0) →
        IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧ IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport B ∪ ⋃ w, (tsupport (C w) ∪ tsupport (E w)),
            ∃ q ∈ Ca, p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (q.1 : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (q.2 : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        τ.IsHaarMeasure →
        Measure.map
            (fun x : Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
                ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
                InfiniteAdeleRing K × InfiniteAdeleRing K))
            τ = τ₀ →
      ∀ J : ℂ, AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
          (fun x : GL (Fin 2) (InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2)))
          (diagUnits2 a (a * t)) τ fa J →

        (∀ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ,
          AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
            AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
          ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (diagUnits2 α β))),
            τ'.IsHaarMeasure →
            AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) (diagUnits2 α β) 1 τ τ' →
          ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.archHaarL K L)
              (fun x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace L, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent L w (AutomorphicForm.archIdentGL K L x) : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2)))
              (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) J' →
            ((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) *
                (J' - (Module.finrank K L : ℂ) * J) =
              B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) :
                ℂ) * C w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ :
                  ℝ) : ℂ) *
                E w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) ∧

        ((¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) δ) →
            ((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) *
                (0 - (Module.finrank K L : ℂ) * J) =
              B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) :
                ℂ) * C w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ :
                  ℝ) : ℂ) *
                E w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) := by sorry
