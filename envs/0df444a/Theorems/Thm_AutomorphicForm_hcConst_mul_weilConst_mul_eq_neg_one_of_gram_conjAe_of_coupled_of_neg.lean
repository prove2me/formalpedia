-- Prove2me | Theorems.Thm_AutomorphicForm_hcConst_mul_weilConst_mul_eq_neg_one_of_gram_conjAe_of_coupled_of_neg
-- name    : AutomorphicForm.hcConst_mul_weilConst_mul_eq_neg_one_of_gram_conjAe_of_coupled_of_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/23dc062f-6a3e-536c-8b8d-3be208e3d03b
-- title:
--   Archimedean sign: Harish-Chandra and Weil constants multiply to -1
-- statement:
--   Fix a Haar measure $\mu_A$ on $\mathrm{GL}_2(\mathbb R)$ (for the Borel structure `glBorelOf ℝ`), a unit $c\in\mathbb R^\times$ with $c<0$, and elements $\delta,y\in\mathrm{GL}_2(\mathbb C\otimes_{\mathbb R}\mathbb R)$ such that $y$ is a norm conjugator for the scalar matrix $c\cdot 1$ and $\delta$ relative to $\sigma=$ `Complex.conjAe`, i.e. the image of $c\cdot 1$ in $\mathrm{GL}_2(\mathbb C\otimes_{\mathbb R}\mathbb R)$ equals $y^{-1}\,N_\sigma(\delta)\,y$. Let $\tau$ be a Haar measure on the centraliser of $c\cdot 1$ in $\mathrm{GL}_2(\mathbb R)$ and $\tau'$ a Haar measure on the twisted ($\sigma$-)centraliser of $\delta$. The hypothesis `hgram` is a common-scale Gram normalisation: there are $\mathbb R$-bases $e_1$ of the image of $M_2(\mathbb R)$ under $x\mapsto 1\otimes x$ and $e_2$ of $\{X: X\delta=\delta\,\sigma(X)\}$ inside $M_2(\mathbb C\otimes_{\mathbb R}\mathbb R)$, and one scalar $s\in(0,\infty)$, such that the pushforward of $\tau$ (resp. $\tau'$) to matrices equals $s$ times the Lebesgue measure transported along the chosen basis, scaled by $\sqrt{|\det(\mathrm{tr}_{\mathbb C\otimes\mathbb R/\mathbb R}\,\mathrm{tr}(e_ie_j))|}$ and given density $|N_{\mathbb R}(\det X)|^{-1}$. Further: $m>0$ with $\mu_A=m\cdot$ (pushforward of $\tau$ to $\mathrm{GL}_2(\mathbb R)$); $u_0\in\mathrm{GL}_2(\mathbb C\otimes_{\mathbb R}\mathbb R)$ and a Haar measure $\tau_S$ on the intersection $S$ of the twisted centralisers of $\delta$ and $u_0\delta$; $\kappa>0$ such that every nonnegative measurable compactly supported $w$ on the twisted centraliser of $\delta$ whose $\tau_S$-integral over each $S$-coset is $1$ satisfies $\int w\,d\tau'=\kappa$; an angle $\theta_1$ and $\gamma_0\in\mathrm{GL}_2(\mathbb R)$ with matrix $c\cdot\begin{pmatrix}\cos\theta_1&-\sin\theta_1\\ \sin\theta_1&\cos\theta_1\end{pmatrix}$, regular semisimple in the sense that $\mathrm{tr}(\gamma_0)^2-4\det(\gamma_0)$ is a unit; $y_0$ a norm conjugator for $\gamma_0$ and $u_0\delta$; a Haar measure $\tau_T$ on the centraliser of $\gamma_0$ with pushforward $\nu_T$ to $\mathrm{GL}_2(\mathbb R)$; a Haar measure $\tau_u$ on the twisted centraliser of $u_0\delta$ whose pushforward to $\mathrm{GL}_2(\mathbb C\otimes_{\mathbb R}\mathbb R)$ agrees with that of $\tau_S$, and which is coupled to $\tau_T$ through $y_0$, meaning that the pushforward of $\tau_u$ under $t\mapsto y_0^{-1}ty_0$ coincides with the pushforward of $\tau_T$ along $\mathrm{GL}_2(\mathbb R)\to\mathrm{GL}_2(\mathbb C\otimes_{\mathbb R}\mathbb R)$; and finally a nonzero real $C$ with the elliptic-transform jump property: for every real normed space $P$, every smooth compactly supported $\Phi$ on $M_2(\mathbb R)\times P$ whose support lies in the locus where $\det$ is a unit, every $p\in P$ and every $r>0$, the quotient $\mathrm{ellipticTransform}(\mathrm{entrySlice}\,\Phi\,p)(r,\theta)/(2\sin\theta)$ tends to some $L$ as $\theta\to 0^+$ and its first-order remainder $(\,\cdot-L)/\theta$ tends to $C\cdot\Phi(r\cdot 1,p)$. The conclusion is the numerical identity $$\Bigl(2\big/\bigl((\mu_A(B)/\nu_T(D))\,C\bigr)\Bigr)\cdot\kappa\cdot m=-1,$$ where $B$ is the Iwasawa box of $g$ of the form $\begin{pmatrix}b_1&b_1x\\0&b_2\end{pmatrix}k$ with $b_1,b_2\in[1,e]$, $x\in[0,1]$ and $k$ in the subgroup `rowIsometrySubgroup₀ ℝ`, and $D=\{g:\det g\in[1,e^2]\}$, both measures being taken as real numbers.
--
--   This is the sign bookkeeping at the real place in the case $c<0$ (the twisted centraliser of the second kind, of quaternionic type): the Harish-Chandra limit constant arising from the elliptic transform, the Weil covolume constant $\kappa$ of the torus $S$ inside the twisted centraliser, and the normalisation factor $m$ combine, under the common Gram normalisation of $\tau$ and $\tau'$, to exactly $-1$. It supplies the numerical input $e=-1$ to the two transfer statements identifying values of orbital integrals at scalar elements with twisted orbital integrals, and it cites the evaluation $C=-8\pi$ of the jump constant together with the Gram-normalised volume computations for the Iwasawa box and the determinant band.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hcConst_mul_weilConst_mul_eq_neg_one_of_gram_conjAe_of_coupled_of_neg.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.hcConst_mul_weilConst_mul_eq_neg_one_of_gram_conjAe_of_coupled_of_neg
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
        (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
               Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
               (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer
               ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
             ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
               (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
             ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)))

    (m : ℝ) (hm0 : 0 < m)
    (hm : μA = ENNReal.ofReal m •
      @Measure.map _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) (glBorelOf ℝ)
        Subtype.val τ)

    (u₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (κ : ℝ) (hκ0 : 0 < κ)
    (hκ : ∀ w : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) → ℝ,
      (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
           twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
       (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
         ∀ t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ),
           ∫ s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)),
             w ((⟨(s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), (Subgroup.mem_inf.mp s.2).1⟩ :
               ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)) * t) ∂τS = 1) →
      (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       ∫ t, w t ∂τ' = κ))

    (θ₁ : ℝ) (γ₀ : GL (Fin 2) ℝ)
    (hγ₀ : ((γ₀ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (c : ℝ) • !![Real.cos θ₁, -Real.sin θ₁; Real.sin θ₁, Real.cos θ₁])
    (hreg : IsRegularSemisimple γ₀)
    (y₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hn₀ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ₀ (u₀ * δ) y₀)
    (τT : @Measure (Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ₀))
    (hτT : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ₀) τT)
    (νT : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hνT : @Measure.map _ _ (centralizerBorel ℝ γ₀) (glBorelOf ℝ) Subtype.val τT = νT)
    (τu : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ))
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)))
    (hτu : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) τu)
    (hτuS : (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
       letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u₀ * δ)
       letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
           twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
       Measure.map Subtype.val τu = Measure.map Subtype.val τS))
    (hcoup : Coupled ℝ ℂ ℝ Complex.conjAe γ₀ (u₀ * δ) y₀ τT τu)

    (C : ℝ) (hC : C ≠ 0)
    (hjump : ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))} →
        ∀ (p : P) (r : ℝ), 0 < r →
          ∃ L : ℂ,
            Filter.Tendsto (fun θ : ℝ => ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds L) ∧
            Filter.Tendsto
              (fun θ : ℝ => (ellipticTransform (entrySlice Φ p) r θ / (2 * Real.sin θ : ℂ) - L) / (θ : ℂ))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds ((C : ℂ) * Φ (Matrix.of.symm (r • (1 : Matrix (Fin 2) (Fin 2) ℝ)), p)))) :
    ((2 : ℝ) / ((μA {g : GL (Fin 2) ℝ | ∃ b₁ ∈ Set.Icc (1 : ℝ) (Real.exp 1), ∃ b₂ ∈ Set.Icc (1 : ℝ) (Real.exp 1),
              ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ k : rowIsometrySubgroup₀ ℝ,
              (g : Matrix (Fin 2) (Fin 2) ℝ) =
                !![b₁, b₁ * x; 0, b₂] * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)}).toReal / (νT {g : GL (Fin 2) ℝ | Matrix.det (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ Set.Icc (1 : ℝ) (Real.exp 2)}).toReal * C)) * κ * m = -1 := by sorry
