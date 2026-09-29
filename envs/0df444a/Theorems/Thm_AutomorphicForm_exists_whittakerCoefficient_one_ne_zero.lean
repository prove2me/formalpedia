-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero
-- name    : AutomorphicForm.exists_whittakerCoefficient_one_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/cf82be52-2134-5580-a435-feffedce0777
-- title:
--   Nonvanishing of the first Whittaker coefficient
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A}_F$; write $\mathrm{GL}_2(\mathbb{A}_F)$ for the adelic general linear group. Fix a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the ideals of $\mathcal{O}_F$, and a family $gen$ of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the height-one primes of $\mathcal{O}_F$; these are assembled by `productionPinsOf`, together with the box $B =$ `AdelicBox.adelicBox F` (the product of a fundamental domain for the lattice $\mathcal{O}_F$ in the infinite adeles with the integral finite adeles), into a package of carrier data whose central character group is taken to be $\top$, whose measure on $\mathrm{GL}_2(\mathbb{A}_F)$ is the Borel Haar measure, and whose measure $\nu$ on $\mathbb{A}_F$ is the adelic additive Haar measure conditioned on $B$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is global in the sense that it is trivial on the principal adeles $\mathrm{im}(F \to \mathbb{A}_F)$, continuous, and not identically $1$. For $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, $\alpha \in F$ and $g \in \mathrm{GL}_2(\mathbb{A}_F)$ the Whittaker coefficient is $$W_\alpha(\varphi)(g) = \int_{\mathbb{A}_F} \varphi\bigl(n(x)\,g\bigr)\,\psi\bigl(-\alpha x\bigr)\,d\nu(x),$$ where $n(x)$ is the unipotent matrix $\begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$ and $\alpha$ is viewed in $\mathbb{A}_F$. Assume $\varphi$ is left invariant under the global points: $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathrm{GL}_2(F)$, embedded entrywise via $F \to \mathbb{A}_F$. Assume further that at a single point $g_0 \in \mathrm{GL}_2(\mathbb{A}_F)$ the constant term vanishes, $W_0(\varphi)(g_0) = 0$; that the slice $x \mapsto \varphi(n(x)g_0)$ is continuous on $\mathbb{A}_F$; that the family $\bigl(W_\alpha(\varphi)(g_0)\bigr)_{\alpha \in F}$ is summable; and that $\varphi(g_0) \neq 0$. Then there exists $g \in \mathrm{GL}_2(\mathbb{A}_F)$ with $W_1(\varphi)(g) \neq 0$.
--
--   This is the genericity step for cusp forms on $\mathrm{GL}_2$ over a number field: a left $\mathrm{GL}_2(F)$-invariant function which is nonzero at some point but has vanishing constant term there has a nonvanishing first Whittaker coefficient, so that its Whittaker expansion is determined by $W_1$. The result is used downstream in the analysis of class sums and growth of automorphic forms, and in the realisation of smooth cusp forms at a point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_one_ne_zero.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField

theorem AutomorphicForm.exists_whittakerCoefficient_one_ne_zero
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hcusp : whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 0 g₀
      = 0)
    (hcont : Continuous (fun x => φ (unipotentGL2 x * g₀)))
    (hsum : Summable (fun α : F =>
      whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ α g₀))
    (hg₀ : φ g₀ ≠ 0) :
    ∃ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 1 g ≠ 0 := by sorry
