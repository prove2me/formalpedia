-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_rightConv_inv_eq_rightConv_rightConv
-- name    : AutomorphicForm.rightConv_rightConv_inv_eq_rightConv_rightConv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/d4765d3a-1890-52cb-9b1c-ae5742dd8846
-- title:
--   Associativity of right convolution on GL₂(A_K)
-- statement:
--   Let $K$ be a number field, and let $G = \mathrm{GL}_2(\mathbb{A}_K)$ be the general linear group of $2\times 2$ matrices over the adele ring of $K$, equipped with its Borel $\sigma$-algebra and the Haar measure $\mu$ given by `AdelicHaar.adelicGLHaar`; for functions $\varphi, f : G \to \mathbb{C}$ write $(\mathrm{rightConv}\,\varphi\,f)(g) = \int_G \varphi(g x)\, f(x)\, d\mu(x)$, which is the operation `rightConv K`. Let $u, g, h : G \to \mathbb{C}$ be such that $u$ is continuous and $g$ and $h$ are continuous with compact support. Then the two functions $\mathrm{rightConv}\,u\,\bigl(\mathrm{rightConv}\,g\,(y \mapsto h(y^{-1}))\bigr)$ and $\mathrm{rightConv}\,(\mathrm{rightConv}\,u\,h)\,g$ on $G$ are equal, i.e. for every $x \in G$,
--   $$\int_G u(xz)\Bigl(\int_G g(zy)\,h(y^{-1})\,d\mu(y)\Bigr)d\mu(z) \;=\; \int_G \Bigl(\int_G u(xyw)\,h(w)\,d\mu(w)\Bigr)g(y)\,d\mu(y).$$
--   Since $z \mapsto \int_G g(zy)h(y^{-1})\,d\mu(y)$ is the ordinary convolution $g \star h$, the identity says that the right-convolution operator attached to $g \star h$ is the operator attached to $h$ followed by the one attached to $g$.
--
--   This is the associativity, in right-convolution form, of the convolution algebra of compactly supported continuous functions on $\mathrm{GL}_2(\mathbb{A}_K)$: $R(g \star h) = R(g) \circ R(h)$. It is used when a test function is written as a sum of convolutions so as to factor the corresponding smoothing operator on automorphic forms into two such operators; it is cited in the Hilbert–Schmidt and trace estimates for kernels built from orthonormal families of forms of a given principal level over a fundamental domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_rightConv_inv_eq_rightConv_rightConv.lean

import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.rightConv_rightConv_inv_eq_rightConv_rightConv
    (K : Type) [Field K] [NumberField K]
    (u g h : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hu : Continuous u)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hh : Continuous h) (hhc : HasCompactSupport h) :
    rightConv K u (rightConv K g fun y => h y⁻¹) = rightConv K (rightConv K u h) g := by sorry
