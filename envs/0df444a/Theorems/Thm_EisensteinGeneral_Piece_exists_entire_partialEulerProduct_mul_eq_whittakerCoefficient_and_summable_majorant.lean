-- Prove2me | Theorems.Thm_EisensteinGeneral_Piece_exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant
-- name    : EisensteinGeneral.Piece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/861cc781-fac1-5038-a8a6-58697b8710a3
-- title:
--   Whittaker coefficients: partial Euler product times entire family
-- statement:
--   Let $F$ be a number field. Let $\psi$ be an additive character of the adele ring of $F$ which is principal-invariant, continuous and nontrivial, given with local components $\psi_v$ at the finite places and levels $n_\psi(v)\in\mathbb Z$, so that $\psi_v$ is trivial on $\{x : |x|_v \le \exp(n_\psi(v))\}$ yet some $x$ with $|x|_v \le \exp(n_\psi(v)+1)$ has $\psi_v(x)\neq 1$, and so that on the finite adeles $\psi$ is the (finitely supported) product of the $\psi_v$; at the infinite places $\psi$ is prescribed, through the identification of the infinite adeles with the mixed space, by nonzero frequencies $\theta_r(i)\in\mathbb R$ at the real places and $\theta_c(w)\in\mathbb C$ at the complex places, via $\prod_i \exp(-2\pi i\,\theta_r(i)p_i)\cdot\prod_w \exp(-4\pi i\,\mathrm{Re}(\theta_c(w)p_w))$. Let $\chi$ be a homomorphism from the ideles to $\mathbb C^\times$, $S$ a finite set of finite places, $\varpi_v$ a uniformiser at each $v$ (valuation $\mathrm{ofAdd}(-1)$), and $\Psi:\mathbb C\to \mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ a family such that each $\Psi_s$ is an induced section: $\Psi_s(bg)=\chi_1(b_{11})\chi_2(b_{22})\Psi_s(g)$ for $b$ in the adelic Borel subgroup, for some characters $\chi_1,\chi_2$ depending on $s$. Let $g\in \mathrm{GL}_2(\mathbb A_F)$ and let $D$ be a `FactorizationDatum F ψv nψ χ ϖ Ψ g S`: a bundle of finite-place data (a conductor exponent function $c_S$, a local-constancy level $m_S$, and finitely many local functions $A_j$, $B_j$, $h_j$), archimedean data (weights, frequencies, triples of exponents and archimedean factors at the real and complex places), an idele $a$, an adele $u$ and scalars $C_j(s)$, subject to conditions including: $|\chi_v(\varpi_v)|=1$ for all $v$; $\chi_v$ unramified and $n_\psi(v)=0$ for $v\notin S$; $c_S(v)\ge 1$ and $\chi_v$ trivial on the higher units of level $c_S(v)$ for $v\in S$; $m_S\ge1$ and local constancy of $A_j$, $B_j$ at level $m_S$; for $v\notin S$ the Tate-type shape $h_j(v,s,x)=\mathbf 1_{\mathcal O_v}(x)+\mathbf 1_{\mathcal O_v^{\,c}}(x)\,\chi_v^{-1}(x)\,|x|_v^{-(2s+1)}$; and further conditions expressing $\Psi$ at $g$ through these local data. The conclusion asserts the existence of a family $Q_\xi:\mathbb C\to\mathbb C$, indexed by the nonzero $\xi\in F$, such that: each $Q_\xi$ is entire; for every nonzero $\xi$ and every $s$ with $\mathrm{Re}\,s>1$, the $\xi$-th Whittaker coefficient at $g$ — the integral $\int \Phi_s(u(x)g)\,\psi(-\xi x)$ against the measure of `productionPins F`, namely the adelic additive Haar measure conditioned to the adelic box, where $\Phi_s(g')=\Psi_s(g')+\sum_{\xi'\in F}\Psi_s(w\,u(\xi')g')$ with $w$ the global Weyl element and $u(\cdot)$ the upper unipotent — equals $\bigl(\prod_{v\notin S}\bigl(1-\chi_v(\varpi_v)\,N(v)^{-(2s+1)}\bigr)\bigr)\cdot Q_\xi(s)$; and for every $R\in\mathbb R$ there is a summable family $M_\xi$ of reals with $\|Q_\xi(s)\|\le M_\xi$ whenever $\|s\|\le R$.
--
--   This is the adelic computation of the Whittaker coefficients of a degenerate Eisenstein series on $\mathrm{GL}_2$: unfolding over the big Bruhat cell, factorising the adelic integral into local integrals, and separating the unramified places into a partial Euler product whose remaining factor is entire in $s$ with a majorant uniform on discs and summable over the frequencies $\xi$. It feeds the statement [`AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein`](thm.html#AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein), where the coefficientwise bounds are assembled into analytic properties of the Eisenstein family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Piece_exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant.lean

import Definitions.Def_EisensteinGeneral_FactorizationDatum
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

open scoped Classical in

theorem EisensteinGeneral.Piece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψ : IsGlobalAddChar F ψ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
    (hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
    (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hθc : ∀ w, θc w ≠ 0)
    (hψarch : ∀ p : mixedEmbedding.mixedSpace F,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
              Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
              Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∀ s, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ s))
    (g : AdelicGL2 (𝓞 F) F)
    (D : FactorizationDatum F ψv nψ χ ϖ Ψ g S) :
    ∃ Q : {ξ : F // ξ ≠ 0} → ℂ → ℂ,
      (∀ ξ : {ξ : F // ξ ≠ 0}, Differentiable ℂ (Q ξ)) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), 1 < s.re →
        whittakerCoefficient F (productionPins F) ψ
            (fun g' => Ψ s g' + ∑' ξ' : F, Ψ s (adelicWeyl (𝓞 F) F
                * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g
          = (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Q ξ s) ∧
      (∀ R : ℝ, ∃ M : {ξ : F // ξ ≠ 0} → ℝ, Summable M ∧
        ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R → ‖Q ξ s‖ ≤ M ξ) := by sorry
