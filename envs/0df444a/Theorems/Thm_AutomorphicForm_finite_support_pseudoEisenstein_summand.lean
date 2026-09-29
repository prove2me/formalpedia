-- Prove2me | Theorems.Thm_AutomorphicForm_finite_support_pseudoEisenstein_summand
-- name    : AutomorphicForm.finite_support_pseudoEisenstein_summand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f8302c9e-a42b-58ce-bffd-a8f2b9840571
-- title:
--   Finiteness of the big-cell sum for a slab profile
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A} =$ `AdeleRing (𝓞 F) F`; let $Z$ be a subgroup of the idele group $\mathbb{A}^\times$ and $\xi\colon Z \to \mathbb{C}^\times$ a group homomorphism. Let $\varphi\colon \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ satisfy `IsSlabProfile F Z ξ φ`, i.e. $\varphi$ is measurable; $\varphi(n(x)g) = \varphi(g)$ for every adele $x$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; $\varphi(\gamma g) = \varphi(g)$ for every $\gamma \in \mathrm{GL}_2(F)$ whose $(1,0)$ entry vanishes, acting through the map $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A})$ induced by $F \to \mathbb{A}$; $\varphi(z \cdot 1 \cdot g) = \xi(z)\varphi(g)$ for $z \in Z$ embedded as a scalar matrix; for all reals $d_1, d_2$ with $0 < d_1$ there is a bound $C$ with $\|\varphi(g)\| \le C$ whenever the idele norm (the module of the distributive Haar character) of $\det g$ lies in $[d_1,d_2]$; and there are reals $a, b$ with $0 < a$ such that $\varphi(g) \neq 0$ forces the adelic height $\mathrm{archHeight} \cdot \mathrm{finHeight}$ of $g$ to lie in $[a,b]$. Then for each $g \in \mathrm{GL}_2(\mathbb{A})$ the set of $\beta \in F$ with $\varphi\bigl(w\,n(\beta)\,g\bigr) \neq 0$ is finite, $w$ being the image in $\mathrm{GL}_2(\mathbb{A})$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   This is the pointwise finiteness of the Bruhat big-cell sum attached to a slab profile: the pseudo-Eisenstein (incomplete theta) series $\varphi(g) + \sum_{\beta \in F} \varphi(w\,n(\beta)\,g)$ reduces at every point to a finite sum. It underlies the computation of the constant term of the pseudo-Eisenstein series and its comparison with the Weyl intertwining integral, the continuity statements for such series, and their compatibility with convolution operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finite_support_pseudoEisenstein_summand.lean

import Definitions.Def_AutomorphicForm_SlabProfile

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open NumberField.AdelicHaar

noncomputable section

theorem AutomorphicForm.finite_support_pseudoEisenstein_summand
    (F : Type) [Field F] [NumberField F]
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (_hφ : AutomorphicForm.IsSlabProfile F Z ξ φ)
    (g : AdelicGL2 (𝓞 F) F) :
    (Function.support fun β : F =>
        φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)).Finite := by sorry
