-- Prove2me | Theorems.Thm_AutomorphicForm_exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary
-- name    : AutomorphicForm.exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/ec34ccd2-dff0-5d4e-9488-53179e718420
-- title:
--   Entire continuation of normalised Whittaker coefficients of flat Eisenstein families
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the real-valued character of the idele group obtained from the distributive Haar character of $\mathbb{A}_F$, assumed pointwise positive. Let $\mu,\nu$ be characters of $\mathbb{A}_F^\times$ into $\mathbb{C}^\times$ that are unitary (of absolute value $1$ at every idele) and trivial on the principal ideles, let $\psi$ be an additive character of $\mathbb{A}_F$ that is continuous, nontrivial and trivial on $F$, and let $\varphi : \mathbb{C} \times \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family such that: each $\varphi_s$ transforms under the adelic Borel subgroup (lower left entry zero) by the characters $\mu\alpha^{s+1/2}$ and $\nu\alpha^{-(s+1/2)}$ applied to the two diagonal entries; at each infinite place the right translates of $\varphi_s$ under the row-isometry subgroup span a finite-dimensional space; the stabiliser of $\varphi_s$ under right translation by the kernel of the archimedean projection is open; $(s,g)\mapsto \varphi_s(g)$ is continuous; $s \mapsto \varphi_s(g)$ is entire for each $g$; and $\varphi_s(k)=\varphi_{s'}(k)$ for all $s,s'$ whenever the finite part of $k$ is integral and each archimedean component of $k$ is a row isometry (flatness). Put $E_s(h) = \varphi_s(h) + \sum_{\xi \in F} \varphi_s(w\,n(\xi)\,h)$, with $w$ the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)$ the upper unipotent. Then there is a finite set $S_0$ of finite places such that for every finite $S \supseteq S_0$ and every family $(\varpi_v)$ of uniformisers (elements of $F_v^\times$ of valuation $\mathrm{ofAdd}(-1)$) there exists $\mathcal{J}_\xi(s,y)$, defined for $\xi \in F \setminus \{0\}$, $s \in \mathbb{C}$ and $y \in \mathbb{A}_F^\times$, with: (i) $s \mapsto \mathcal{J}_\xi(s,y)$ entire; (ii) for $\operatorname{Re} s > 1$, $\mathcal{J}_\xi(s,y)$ equals the product of $\prod_{v \notin S}(1 - (\mu\nu^{-1})_v(\varpi_v)\,N(v)^{-(2s+1)})^{-1}$ with the $\psi$-Whittaker coefficient $\int \! E_s(n(x)\,\mathrm{diag}(y,1))\,\psi(-\xi x)$ taken with respect to the measure of the production pins; (iii) joint continuity of $(s,y) \mapsto \mathcal{J}_\xi(s,y)$; (iv) $\mathcal{J}_\xi(s,\eta y) = \mathcal{J}_{\xi\eta}(s,y)$ for $\eta \in F^\times$; and (v) for all compact $C \subseteq \mathbb{C}$ and compact $U \subseteq \mathbb{A}_F^\times$ there are $k \in \mathbb{N}$, a fractional ideal $I$, a bound $A$ and a function $q$ with $|q(s)| \le A$ on $C$, such that for every $N$ there is $c$ with: for $s \in C$, $u \in U$, every idele $z$ with trivial finite part and all archimedean components equal to a given $r > 0$, and every nonzero $\xi$, one has $\mathcal{J}_\xi(s,zu) = 0$ unless $\xi \in I$, and $\|\mathcal{J}_\xi(s,zu)\| \le c\, r^{[F:\mathbb{Q}](1/2 - q(s))} \max(1,|N_{F/\mathbb{Q}}\xi|)^k \prod_{w \text{ real}} (1+r|\xi_w|)^{-N} \prod_{w \text{ complex}} (1+r\|\xi_w\|)^{-2N}$, the components $\xi_w$ being those of the mixed embedding.
--
--   This is the analytic input for the Fourier–Whittaker expansion of the Eisenstein series attached to a flat family of Borel-induced sections of two unitary idele class characters: after normalisation by the partial Hecke $L$-factor $L^S(2s+1,\mu\nu^{-1})$, each Whittaker coefficient along the diagonal torus continues to an entire function of $s$ with bounds on compacta that factorise over the infinite places and decay rapidly in $\xi$. It is used in the construction of the continued Bruhat–Eisenstein series, where the coefficients are summed over $\xi \in F^\times$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.InfinitePlace AutomorphicForm
open AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

open scoped Classical in

theorem AutomorphicForm.exists_entire_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), S₀ ⊆ S →
      ∀ (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
        (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) →
      ∃ 𝒥 : {ξ : F // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ,
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ),
          Differentiable ℂ (fun s => 𝒥 ξ s y)) ∧
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ), 1 < s.re →
          𝒥 ξ s y
            = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                  * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹)
              * whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) (diagOne y)) ∧
        (∀ ξ : {ξ : F // ξ ≠ 0}, Continuous (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => 𝒥 ξ p.1 p.2)) ∧
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ),
          𝒥 ξ s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
            = 𝒥 ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y) ∧
        (∀ (C : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact C → IsCompact U →
          ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (A : ℝ) (q : ℂ → ℝ),
            (∀ s ∈ C, |q s| ≤ A) ∧
            ∀ N : ℕ, ∃ c : ℝ,
              ∀ s ∈ C, ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r →
                (z : AdeleRing (𝓞 F) F).2 = 1 →
                (∀ w : InfinitePlace F,
                  Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
                ∀ ξ : {ξ : F // ξ ≠ 0},
                  ((ξ : F) ∉ I → 𝒥 ξ s (z * u) = 0) ∧
                  ‖𝒥 ξ s (z * u)‖ ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - q s)) *
                    (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                    (∏ w : {w : InfinitePlace F // w.IsReal},
                      (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                    ∏ w : {w : InfinitePlace F // w.IsComplex},
                      (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ))) := by sorry
