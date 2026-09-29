-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String
-- name    : AutomorphicForm.exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/904e8d90-09cb-5033-b145-9351dbf49cd8
-- title:
--   Rank-one torus Whittaker functions of a complex-place SU(2)-string
-- statement:
--   Let $K$ be a number field, $D \subseteq \mathrm{GL}_2(\mathbb{A}_K)$, and let the carrier data be `productionPinsOf K D` with level subgroups $N \mapsto \mathtt{levelOne}\ N \cap \ker(\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(\mathbb{A}_{K,\infty}))$, Hecke generators $v \mapsto \mathtt{heckeGen}\ v$ and the adelic box; its central subgroup is all of $(\mathbb{A}_K)^\times$, its measure on $\mathbb{A}_K$ is additive Haar measure conditioned on the box. Let $\xi$ be a character of $(\mathbb{A}_K)^\times$ with $|\xi(z)| = \|z\|^{w_0}$ for the idele norm, and $w$ a complex place. Let $x_0,\dots,x_n \colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, invariant under left translation by $\mathrm{GL}_2(K)$, with $x_p(\mathrm{diag}(z,z)g) = \xi(z)x_p(g)$; every word in the six flow-derivatives $H,E,F,iH,iE,iF$ at $w$ applied to $x_p$ is continuous and smooth along the lifted $\mathrm{GL}_2(\mathbb{C})$-directions at $w$; $x_p$ has circle weight $n-2p$ at $w$. Given matrix-valued $E_1,E_2$ on $\mathbb{R}$ with $E_i(0)=1$ and $E_i'(0)$ the stated ladder matrices (entries $1$, $-j(n+1-j)$, resp. $\mathrm{i}$, $\mathrm{i}\,j(n+1-j)$), right translation at $w$ by $\begin{pmatrix}\cos s & -\sin s\\ \sin s & \cos s\end{pmatrix}$ and $\begin{pmatrix}\cos s & \mathrm{i}\sin s\\ \mathrm{i}\sin s & \cos s\end{pmatrix}$ acts on the string through $E_1(s)$, $E_2(s)$; the two Casimir operators at $w$ act on every $x_p$ by scalars $\lambda$, $\lambda'$; and each Whittaker integral $W(x_p)(g)=\int_{\mathbb{A}_K} x_p(u(t)g)\psi_K(-t)\,d\nu(t)$ satisfies $|W(x_p)(g)| \le C_0 \|\det g\|^{w_0/2}$. Then there are functions $\varphi_0,\dots,\varphi_n \colon K_w \to \mathbb{C}$ such that for every idele $b$ with trivial finite part there is a constant $c_b \in \mathbb{C}$ with $W(x_p)(\mathrm{diag}(a,1)) = c_b\,\varphi_p(a_w)$ for all $p$ and all ideles $a$ with trivial finite part agreeing with $b$ at every infinite place other than $w$.
--
--   This is the rank-one (multiplicity-one) statement for the one-variable torus Whittaker functions attached to an $SU(2)$-string at a complex place: as the coordinates away from $w$ are frozen, the $n+1$ functions of $a_w$ are all proportional to fixed functions $\varphi_p$ with a single constant depending only on the frozen data, no unitarity being assumed. It feeds the description of the Whittaker coefficients of a cuspidal constituent at a complex place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String.lean

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

theorem AutomorphicForm.exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String
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
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) :
    ∃ φ : Fin (n + 1) → w.Completion → ℂ,
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 → ∃ cb : ℂ, ∀ p : Fin (n + 1),
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
              (diagOne a) = cb * φ p (((a : AdeleRing (𝓞 K) K)).1 w) := by sorry
