-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses
-- name    : AutomorphicForm.whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/03bfcad1-2f50-53ee-a74a-c29a45341490
-- title:
--   Hypotheses of the GL₂(ℂ) Whittaker system for an SU(2)-string
-- statement:
--   Let $K$ be a number field, let $D$ be a subset of $GL_2(\mathbb{A}_K)$, let $w$ be an infinite place of $K$ with `hw : w.IsComplex`, and let $g_0 \in GL_2(\mathbb{A}_K)$. Throughout, `archComplexGLAt hw` denotes the monoid homomorphism $GL_2(\mathbb{C}) \to GL_2(\mathbb{A}_K)$ obtained from the inverse of the identification of $K_w$ with $\mathbb{C}$ followed by the inclusion of $GL_2(K_w)$ at the place $w$, and `archComplexLiftAt hw` extends it to arbitrary $2\times 2$ complex matrices $e$ by sending $e$ to the image of $e$ when $\det e \neq 0$ and to $1$ otherwise. For a direction $d$ in the six-element type `ArchDirComplex` $= \{H, E, F_m, iH, iE, iF_m\}$, `archFlowMatrixComplex d t` is the corresponding one-parameter matrix ($\operatorname{diag}(e^{t}, e^{-t})$, $\binom{1\ t}{0\ 1}$, $\binom{1\ 0}{t\ 1}$ for $H, E, F_m$, and the same with $t$ replaced by $it$ for $iH, iE, iF_m$), and $D_d\varphi(g) = \frac{d}{dt}\varphi\bigl(g\cdot \mathrm{archComplexGLAt}\,hw\,(\mathrm{archFlowMatrixComplex}\,d\,t)\bigr)\big|_{t=0}$ is `archDerivAtComplex hw d`. The data are: a natural number $n$ and a family $x_0, \dots, x_n$ of functions $GL_2(\mathbb{A}_K) \to \mathbb{C}$, two matrix-valued functions $E_1, E_2 : \mathbb{R} \to M_{n+1}(\mathbb{C})$, and two scalars $\lambda, \lambda' \in \mathbb{C}$. The hypotheses on them are the following. `hxc`: each $x_p$ is continuous. `hxG`: each $x_p$ is invariant under left translation by the image of $GL_2(K)$ in $GL_2(\mathbb{A}_K)$ under `globalPoints`. `hreg`: for every $p$ and every list $l$ of directions, the iterated derivative obtained by applying the operators $D_d$ for the entries of $l$ in turn (the head of $l$ outermost) to $x_p$ is continuous and satisfies `IsArchSmoothAtComplex hw`, i.e. for every $g \in GL_2(\mathbb{A}_K)$ the map $e \mapsto \varphi(g \cdot \mathrm{archComplexLiftAt}\,hw\,e)$ is $C^\infty$ over $\mathbb{R}$ on the set of $2\times 2$ complex matrices of nonzero determinant. `hwt`: each $x_p$ has circle weight $n - 2p$ at $w$, that is, $x_p(g \cdot \mathrm{archComplexGLAt}\,hw\,\operatorname{diag}(\zeta, \zeta^{-1})) = \zeta^{\,n-2p} x_p(g)$ for every unit $\zeta \in \mathbb{C}^\times$ with $\|\zeta\| = 1$ and every $g$. `hK₁` and `hK₂`: for all $p$, all $s \in \mathbb{R}$ and all $g$,
--   $$x_p\Bigl(g \cdot \mathrm{archComplexLiftAt}\,hw \begin{pmatrix} \cos s & -\sin s \\ \sin s & \cos s\end{pmatrix}\Bigr) = \sum_{p'} (E_1 s)_{p' p}\, x_{p'}(g), \qquad x_p\Bigl(g \cdot \mathrm{archComplexLiftAt}\,hw \begin{pmatrix} \cos s & i\sin s \\ i\sin s & \cos s\end{pmatrix}\Bigr) = \sum_{p'} (E_2 s)_{p' p}\, x_{p'}(g),$$
--   the entries being the real cosine and sine of $s$ viewed in $\mathbb{C}$. `hcas`: for every $p$, $\mathrm{archCasimirAtComplex}\,hw\,(x_p) = \lambda\, x_p$ and $\mathrm{archCasimirBarAtComplex}\,hw\,(x_p) = \lambda'\, x_p$, where, writing $\partial_d = \tfrac12(D_d - i D_{id})$ and $\bar\partial_d = \tfrac12(D_d + i D_{id})$ for $d \in \{H, E, F_m\}$, the two Casimir operators are $-\bigl(\tfrac14 \partial_H\partial_H - \tfrac12 \partial_H + \partial_E\partial_{F_m}\bigr)$ and $-\bigl(\tfrac14 \bar\partial_H\bar\partial_H - \tfrac12 \bar\partial_H + \bar\partial_E\bar\partial_{F_m}\bigr)$. The conclusion concerns the first Whittaker coefficient for the carrier data `productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)` and the standard global additive character $\psi =$ [`NumberField.StandardAddChar.stdAddChar K`](def/NumberField_AdelicTraceFin.html#L198) of $\mathbb{A}_K$. Of that carrier datum the Whittaker coefficient uses only the additive measure, namely the adelic additive Haar measure conditioned on the box `adelicBox K` (infinite part in the fundamental domain of the lattice basis, finite part the integral finite adeles); the level subgroups `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and the Hecke generators `heckeGen (𝓞 K) K v` are carried along as data. Explicitly, for $\varphi : GL_2(\mathbb{A}_K) \to \mathbb{C}$ and $g \in GL_2(\mathbb{A}_K)$ the coefficient at $\alpha \in K$ is $\int \varphi\bigl(\binom{1\ x}{0\ 1} g\bigr)\psi(-(\alpha x))\,d\nu(x)$ over $x \in \mathbb{A}_K$. Abbreviate, for $\varphi : GL_2(\mathbb{A}_K) \to \mathbb{C}$ and $h \in GL_2(\mathbb{C})$,
--   $$\mathcal{W}[\varphi](h) := \text{the coefficient at } \alpha = 1 \text{ of } \varphi \text{ at } g_0 \cdot \mathrm{archComplexGLAt}\,hw\,h .$$ The assertion is the conjunction of eight clauses. (1) For all $p$, every direction $d$ and every $h \in GL_2(\mathbb{C})$, the function $t \mapsto \mathcal{W}[x_p](h \cdot \mathrm{archFlowMatrixComplex}\,d\,t)$ has derivative $\mathcal{W}[D_d x_p](h)$ at $t = 0$. (2) For all $p$, all directions $d, d'$ and every $h$, the function $t \mapsto \mathcal{W}[D_d x_p](h \cdot \mathrm{archFlowMatrixComplex}\,d'\,t)$ has derivative $\mathcal{W}[D_{d'} D_d x_p](h)$ at $t = 0$. (3) For all $p$ and every $h$,
--   $$-\Bigl(\tfrac14\Bigl(\tfrac12\bigl(\tfrac12(\mathcal{W}[D_HD_Hx_p](h) - i\,\mathcal{W}[D_HD_{iH}x_p](h)) - i\,\tfrac12(\mathcal{W}[D_{iH}D_Hx_p](h) - i\,\mathcal{W}[D_{iH}D_{iH}x_p](h))\bigr)\Bigr) - \tfrac12\cdot\tfrac12\bigl(\mathcal{W}[D_Hx_p](h) - i\,\mathcal{W}[D_{iH}x_p](h)\bigr) + \tfrac12\Bigl(\tfrac12(\mathcal{W}[D_ED_{F_m}x_p](h) - i\,\mathcal{W}[D_ED_{iF_m}x_p](h)) - i\,\tfrac12(\mathcal{W}[D_{iE}D_{F_m}x_p](h) - i\,\mathcal{W}[D_{iE}D_{iF_m}x_p](h))\Bigr)\Bigr) = \lambda\, \mathcal{W}[x_p](h),$$
--   which is the relation $\mathrm{archCasimirAtComplex}$ written out term by term on the Whittaker side. (4) For all $p$ and every $h$, the same expression with every inner difference replaced by the corresponding sum and every factor $-i$ in front of the bracketed halves replaced by $+i$ (the outer pattern $-(\tfrac14(\cdot) - \tfrac12(\cdot) + \tfrac12(\cdot))$ being unchanged), equals $\lambda'\,\mathcal{W}[x_p](h)$; this is the conjugate Casimir relation written out term by term. (5) For all $p$, every $z \in \mathbb{C}$ and every $h$,
--   $$\mathcal{W}[x_p]\bigl(\tbinom{1\ z}{0\ 1}\cdot h\bigr) = \exp\bigl(2\pi i\,\cdot\,2\operatorname{Re}(1\cdot z)\bigr)\,\mathcal{W}[x_p](h),$$
--   the exponent being the real number $2\operatorname{Re}(1\cdot z)$ viewed in $\mathbb{C}$. (6) For all $p$, every unit $\zeta \in \mathbb{C}^\times$ with $\|\zeta\| = 1$ and every $h$, $\mathcal{W}[x_p](h \cdot \operatorname{diag}(\zeta, \zeta^{-1})) = \zeta^{\,n-2p}\,\mathcal{W}[x_p](h)$. (7) For all $p$, every $s \in \mathbb{R}$ and all $h, k \in GL_2(\mathbb{C})$ whose underlying matrix of $k$ equals $\begin{pmatrix} \cos s & -\sin s \\ \sin s & \cos s\end{pmatrix}$ (complex cosine and sine at the real argument $s$), $\mathcal{W}[x_p](h k) = \sum_{p'} (E_1 s)_{p' p}\,\mathcal{W}[x_{p'}](h)$. (8) For all $p$, every $s \in \mathbb{R}$ and all $h, k \in GL_2(\mathbb{C})$ whose underlying matrix of $k$ equals $\begin{pmatrix} \cos s & i\sin s \\ i\sin s & \cos s\end{pmatrix}$, $\mathcal{W}[x_p](h k) = \sum_{p'} (E_2 s)_{p' p}\,\mathcal{W}[x_{p'}](h)$.
--
--   This is the instantiation lemma that transports an $SU(2)$-string of adelic automorphic functions at a complex place $w$ to the functions $h \mapsto \mathcal{W}[x_p](h)$ on $GL_2(\mathbb{C})$, verifying for them the full list of hypotheses — first- and second-order flow-derivative identities, the two Casimir equations, unipotent covariance, circle weight and the two compact $K$-type relations — required by the torus Whittaker differential system on $GL_2(\mathbb{C})$. It is used by [`AutomorphicForm.exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String`](thm.html#AutomorphicForm.exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String), where the resulting coupled second-order system along the split torus is solved.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses.lean

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

theorem AutomorphicForm.whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (g₀ : AdelicGL2 (𝓞 K) K) (_hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₂ s p' p * x p' g)
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p) :
    (∀ (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t))) (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g₀ * archComplexGLAt hw h)) 0) ∧
    (∀ (p : Fin (n + 1)) (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d' t))) (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' (archDerivAtComplex hw d (x p))) 1 (g₀ * archComplexGLAt hw h)) 0) ∧
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g₀ * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h))))) = lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g₀ * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h))))) = lam' * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (z : ℂ) (h : GL (Fin 2) ℂ),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (unipotentGL2 z * h)) = Complex.exp (2 * Real.pi * Complex.I * ((2 * ((1 : ℂ) * z).re : ℝ) : ℂ)) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * circleGL2 ζ)) = (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) = ∑ p' : Fin (n + 1), E₁ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) = ∑ p' : Fin (n + 1), E₂ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) := by sorry
