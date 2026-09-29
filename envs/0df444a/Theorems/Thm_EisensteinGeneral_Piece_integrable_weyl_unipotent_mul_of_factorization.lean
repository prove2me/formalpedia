-- Prove2me | Theorems.Thm_EisensteinGeneral_Piece_integrable_weyl_unipotent_mul_of_factorization
-- name    : EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/92217f3d-47b6-5e3b-85b0-5511e12a23d0
-- title:
--   Adelic integrability of big-cell values for Re s>1
-- statement:
--   Let $F$ be a number field. Fix, for every finite place $v$ of $F$ (a height-one prime of $\mathcal O_F$), an additive character $\psi_v$ of the completion $F_v$ with values in $\mathbb C$, an integer $n_\psi(v)$, and an element $\varpi_v \in F_v^{\times}$ with $v(\varpi_v)$ equal to $\mathrm{ofAdd}(-1)$, i.e. of the valuation of a uniformiser; fix a character $\chi$ of the ideles, that is a monoid homomorphism from the units of the adele ring of $F$ to $\mathbb C^{\times}$, a finite set $S$ of finite places, a family $\Psi \colon \mathbb C \to \mathrm{GL}_2(\mathbb A_F) \to \mathbb C$ and a point $g \in \mathrm{GL}_2(\mathbb A_F)$. Assume given a term $D$ of the structure `FactorizationDatum` for these data, whose fields provide a level function $c_S$ on finite places and an integer $m_S$, a number $n$ of terms, finite-place functions $A$, $B$ and $h$ indexed by $j < n$, archimedean data at the real places (integers, real shifts and weight functions $W_r$) and at the complex places (triples of naturals, real shifts and weight functions $W_c$), an idele $a$, an adele $u$ and scalar functions $C_j \colon \mathbb C \to \mathbb C$, subject to conditions including: $\|\chi_v(\varpi_v)\| = 1$ at every $v$, where $\chi_v$ denotes the local component of $\chi$; $\chi_v$ trivial on units of valuation $1$ for $v \notin S$; $n_\psi(v) = 0$ for $v \notin S$; $1 \le c_S(v)$ for $v \in S$ and $\chi_v$ trivial on the higher unit group of level $c_S(v)$ there; $1 \le m_S$; local constancy of each $A_j(v,\cdot)$ on the valuation ring and of each $B_j(v,\cdot)$ on $F_v$, at radius $\mathrm{ofAdd}(-m_S)$; and, for $v \notin S$, the prescription of $h_j(v,s,\cdot)$ as the unramified integrand, namely the indicator of the integers of $F_v$ plus, off that set, $\chi_v^{-1}(y)\,|y|_v^{-(2s+1)}$; the remaining conditions of the structure tie the values of $\Psi$ at $g$ to these local data. Then for every $s \in \mathbb C$ with $1 < \operatorname{Re} s$, the function $y \mapsto \Psi(s)(w\, n(y)\, g)$ is integrable over the adele ring of $F$ for additive Haar measure, where $w$ is the image in $\mathrm{GL}_2(\mathbb A_F)$ of the antidiagonal matrix $\begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$ over $F$ and $n(y) = \begin{pmatrix} 1 & y \\ 0 & 1\end{pmatrix}$.
--
--   This is the convergence statement underlying the Whittaker coefficients of Eisenstein series on $\mathrm{GL}_2$ in the region $\operatorname{Re} s > 1$: on the big Bruhat cell the integrand factorises into archimedean weight functions and local Tate-type integrands, and the product is absolutely integrable over the adeles. It is used to justify the unfolding of the Whittaker integral into an Euler product in the results computing Whittaker coefficients of the Bruhat–Eisenstein family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Piece_integrable_weyl_unipotent_mul_of_factorization.lean

import Definitions.Def_EisensteinGeneral_FactorizationDatum
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization
    (F : Type) [Field F] [NumberField F]
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F)
    (D : FactorizationDatum F ψv nψ χ ϖ Ψ g S) :
    ∀ s : ℂ, 1 < s.re →
      Integrable (fun y => Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F) := by sorry
