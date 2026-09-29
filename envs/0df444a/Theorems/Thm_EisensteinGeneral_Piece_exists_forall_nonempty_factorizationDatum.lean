-- Prove2me | Theorems.Thm_EisensteinGeneral_Piece_exists_forall_nonempty_factorizationDatum
-- name    : EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/79426fc0-2e69-5917-8896-b698fdc64644
-- title:
--   Factorisation data exist for flat nonzero induced families
-- statement:
--   Let $F$ be a number field, and let $\alpha$ denote the character of the idele group $(\mathbb{A}_F)^\times$ with values in $\mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring $\mathbb{A}_F$ by composing with $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units; assume $\alpha$ takes positive values. Let $\mu,\nu$ be continuous characters $(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ that are unitary, i.e. $\lVert\mu(x)\rVert=\lVert\nu(x)\rVert=1$ for all $x$, and set $\chi=\mu\nu^{-1}$. Let $\psi$ be an additive character of $\mathbb{A}_F$ which is continuous, nontrivial and invariant under the principal adeles, given with local components $\psi_v$ at the finite places and integers $n_\psi(v)$ of finite support such that $\psi_v$ is trivial on elements of valuation at most $\exp(n_\psi(v))$ but nontrivial at some element of valuation at most $\exp(n_\psi(v)+1)$, such that the restriction of $\psi$ to the finite adeles is the (finitary) product of the $\psi_v$, and such that on the mixed space its archimedean part is the prescribed product of exponentials with nonzero real frequencies $\theta_r(w)$ at the real places and nonzero complex frequencies $\theta_c(w)$ at the complex places. Let $\varpi_v$ be a uniformiser at each finite place, of valuation $-1$. Let $\Psi:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy: for each $s$, $\Psi_s$ is a section induced from the pair $(\mu\,\alpha^{s+1/2},\ \nu\,\alpha^{-(s+1/2)})$, that is $\Psi_s(bg)$ equals the product of these two characters evaluated at the two diagonal entries of $b$ times $\Psi_s(g)$ for $b$ in the adelic Borel subgroup; $\Psi_s$ is finite under the row-isometry subgroup at each infinite place and smooth under the finite adelic maximal compact; $\Psi$ is jointly continuous and, for fixed $g$, entire in $s$; $\Psi$ is flat, i.e. $\Psi_s(k)=\Psi_{s'}(k)$ whenever the finite part of $k$ is integral and each archimedean component of $k$ is a row isometry; and $\Psi$ is not identically zero. Then for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ there is a finite set $S_0$ of finite places of $F$ such that for every finite set $S\supseteq S_0$ the type $\mathtt{FactorizationDatum}\ F\ \psi_v\ n_\psi\ \chi\ \varpi\ \Psi\ g\ S$ is nonempty: there exist depths $c_S$, a common level $m_S\ge 1$, finitely many terms with local functions $A,B,h$ at the finite places, integral weights and real twists at the real places, triples of exponents and real twists at the complex places, archimedean Whittaker-type functions, an idele $a$, an adele $u$ and entire scalars $C$, satisfying the compatibility conditions recorded in that structure (among them $\lVert\chi_v(\varpi_v)\rVert=1$, triviality of $\chi_v$ on units and $n_\psi(v)=0$ off $S$, triviality of $\chi_v$ on the higher unit groups of depth $c_S(v)$ for $v\in S$, local constancy of $A$ and $B$ at level $m_S$, and the prescribed unramified form of $h$ off $S$; summarised here).
--
--   This is the global factorisation (pure tensor decomposition) of a nonzero flat, $K$-finite family of induced sections on $\mathrm{GL}_2$ of the adeles at an arbitrary point $g$, obtained from the Iwasawa decomposition $g=bk$ and the transformation law of induced sections. It is the input to the computation of Whittaker coefficients of Bruhat–Eisenstein series and to the resulting partial Euler product and intertwining-integral identities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Piece_exists_forall_nonempty_factorizationDatum.lean

import Definitions.Def_EisensteinGeneral_FactorizationDatum
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped NNReal

open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel in
open scoped Classical in

theorem EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμc : Continuous μ) (_hνc : Continuous ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
      (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
      (_hnψfin : (Function.support nψ).Finite)
      (_hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
      (_hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
        ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
      (_hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
        ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
      (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
      (_hθr : ∀ i, θr i ≠ 0)
      (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
      (_hθc : ∀ w, θc w ≠ 0)
      (_hψarch : ∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
        Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
        * ∏ w : {w : InfinitePlace F // w.IsComplex},
        Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
      (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχ : χ = μ * ν⁻¹)
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
      (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hΨ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (Ψ s))
      (_hΨK : ∀ s, IsArchKFinite F (Ψ s))
      (_hΨf : ∀ s, IsKfSmooth F (Ψ s))
      (_hΨjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ψ p.1 p.2))
      (_hΨhol : ∀ g, Differentiable ℂ (fun s => Ψ s g))
      (_hΨflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          Ψ s k = Ψ s' k)
      (_hΨne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), Ψ s g ≠ 0)
      (g : AdelicGL2 (𝓞 F) F),
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S →
      Nonempty (FactorizationDatum F ψv nψ χ ϖ Ψ g S) := by sorry
