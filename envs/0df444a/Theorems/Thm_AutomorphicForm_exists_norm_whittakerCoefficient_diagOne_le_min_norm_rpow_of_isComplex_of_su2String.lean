-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String
-- name    : AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/9163edd4-ceea-5103-b3ad-7e8b1978897e
-- title:
--   Whittaker decay at a complex place for an SU(2)-string
-- statement:
--   Let $K$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, and let the carrier data be `productionPinsOf` for $D$, the level subgroups $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$, the Hecke generators $v \mapsto \mathrm{heckeGen}(v)$ and the box $\mathrm{adelicBox}(K)$; its central subgroup is all of $(\mathbb{A}_K)^\times$, and its measure on $\mathbb{A}_K$ is additive Haar measure conditioned on $\mathrm{adelicBox}(K)$. Let $\xi$ be a character of $(\mathbb{A}_K)^\times$ with values in $\mathbb{C}^\times$ with $|\xi(z)| = \|z\|^{w_0}$ for a real $w_0$, where $\|\cdot\|$ is the module of the scaling action on adelic Haar measure, and let $w$ be a complex place. Let $x_0,\dots,x_n : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous, invariant under left translation by the image of $\mathrm{GL}_2(K)$, and satisfy $x_p(z g) = \xi(z)\,x_p(g)$ for central ideles $z$. Assume: every word in the six flow directions $H,E,F,iH,iE,iF$ at $w$ applied to $x_p$ is again continuous and smooth along the matrix coordinates at $w$; each $x_p$ has circle weight $n-2p$ at $w$; the matrix functions $E_1,E_2 : \mathbb{R} \to \mathbb{C}^{(n+1)\times(n+1)}$ satisfy $E_i(0)=1$ with derivatives at $0$ given by the stated ladder matrices, and right translation at $w$ by $\begin{pmatrix}\cos s & -\sin s\\ \sin s & \cos s\end{pmatrix}$, respectively $\begin{pmatrix}\cos s & i\sin s\\ i\sin s & \cos s\end{pmatrix}$, transforms the tuple $(x_p)$ by $E_1(s)$, respectively $E_2(s)$; the two Casimir operators at $w$ act on each $x_p$ by scalars $\lambda$, $\lambda'$; each Whittaker coefficient $W_1(x_p)$, taken with the standard additive character and $\alpha = 1$, satisfies $|W_1(x_p)(g)| \le C_0 \|\det g\|^{w_0/2}$; $\lambda' = \bar\lambda$; if $\lambda' = \lambda$ and $\lambda$ is real then $n = 0$ or $\lambda > -(n^2+4n)/16$; and if $\lambda = 0$ and $n = 0$ then $x_0$ is invariant under right translation by the determinant-one matrices at $w$. Finally let $b$ be an idele with trivial finite part. Then there are $\delta > 0$ and a constant $C$ such that for every $p$ and every idele $a$ with trivial finite part whose infinite components agree with those of $b$ at all infinite places other than $w$, $$|W_1(x_p)(\mathrm{diag}(a,1))| \le C\,\|a_w\|^{m_w w_0/2}\,\min(1,\|a_w\|)^{\delta},$$ where $m_w$ is the multiplicity of $w$.
--
--   This is the complex-place case of the archimedean decay of Whittaker functions along the diagonal torus, stated for a whole $SU(2)$-string of $K$-finite vectors at once rather than for a single form, the decay being uniform over the string and over ideles varying only at $w$. It is used to supply the complex-place input of the archimedean decay estimate for cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hE₁ : E₁ 0 = 1) (hE₂ : E₂ 0 = 1)
    (hE₁' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
      (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hE₂' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
      (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₂ s p' p * x p' g)
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p)
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (hU : lam' = (starRingEnd ℂ) lam)
    (hR : lam' = lam → lam.im = 0 → n = 0 ∨ -(((n : ℝ) ^ 2 + 4 * (n : ℝ)) / 16) < lam.re)
    (hZ : lam = 0 → n = 0 → ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ),
      Matrix.GeneralLinearGroup.det h = 1 → x 0 (g * archComplexGLAt hw h) = x 0 g)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ p : Fin (n + 1),
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
              (diagOne a)‖ ≤
          C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ := by sorry
