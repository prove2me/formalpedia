-- Prove2me | Theorems.Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level
-- name    : CuspForm.IsEigenformWith.heckeU_degeneracy_of_dvd_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/bc73a24e-7afa-58e7-ab4f-c5ce3d1678a4
-- title:
--   U_q on the degeneracy string of an eigenform
-- statement:
--   Let $M$ and $L$ be non-zero natural numbers with $L \mid M$, let $k \in \mathbb{Z}$, let $\varepsilon_L$ be a Dirichlet character mod $L$ with values in $\mathbb{C}$, and let $g$ be a cusp form of weight $k$ for $\Gamma_1(L)$ satisfying [`CuspForm.IsEigenformWith`](def/CuspForm_PrimitiveFormGamma1.html#L19) $\varepsilon_L$: its $q$-expansion coefficients (taken with width $1$) satisfy $a_1(g) = 1$, for every prime $p \nmid L$ and every $n$ one has $a_{pn}(g) + \varepsilon_L(p) p^{k-1} a_{n/p}(g) = a_p(g) a_n(g)$ (the middle term read as $0$ unless $p \mid n$), for every prime $\ell \mid L$ and every $n$ one has $a_{\ell n}(g) = a_\ell(g) a_n(g)$, and $g$ has nebentypus $\varepsilon_L$, i.e. $g(\gamma \tau) = \varepsilon_L(\gamma_{11}) (\gamma_{10}\tau + \gamma_{11})^k g(\tau)$ for all $\gamma \in \Gamma_0(M)$ — here for $\gamma \in \Gamma_0(L)$. Let $G$ be a family of cusp forms of weight $k$ for $\Gamma_1(M)$ indexed by the naturals such that for every $d \mid M/L$ and every $\tau$ in the upper half-plane $G_d(\tau) = g(\mathrm{diag}(d,1)\tau)$, i.e. $G_d(\tau) = g(d\tau)$. Let $q$ be a prime dividing $M$ and let $d \mid M/L$. With $U_q F = \sum_{j<q} F \mid_k \begin{pmatrix} 1 & j \\ 0 & q\end{pmatrix}$, the conclusion asserts three identities of functions on the upper half-plane: if $q \mid d$ then $U_q G_d = G_{d/q}$; if $q \nmid d$ and $q \mid L$ then $U_q G_d = a_q(g) G_d$; and if $q \nmid d$ and $q \nmid L$ then $U_q G_d = a_q(g) G_d - \varepsilon_L(q) q^{k-1} G_{dq}$.
--
--   This is the standard computation of the Atkin–Lehner operator $U_q$, for $q \mid M$, on the string of degeneracy (oldform) translates $G_d(\tau) = g(d\tau)$ of a normalised eigenform $g$ of level $L \mid M$, in the three cases according to whether $q$ divides $d$ and whether $q$ divides $L$. It shows that the old class spanned by the $G_d$ with $d \mid M/L$ is stable under the $U_q$, and is used in the analysis of generalised eigenspaces of Hecke operators on cusp forms for $\Gamma_H$ and in the construction of bases of primitive forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean

import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.IsEigenformWith.heckeU_degeneracy_of_dvd_level
    (M : ℕ) [NeZero M] (k : ℤ) {L : ℕ} [NeZero L] (hLM : L ∣ M)
    {εL : DirichletCharacter ℂ L} {g : CuspForm (CongruenceSubgroup.Gamma1 L) k}
    (hg : CuspForm.IsEigenformWith εL g)
    (G : ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ d : ℕ, d ∣ M / L → ∀ τ : UpperHalfPlane, G d τ = g (ModularForm.heckeDiagMatrix d • τ))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) {d : ℕ} (hd : d ∣ M / L) :
    (q ∣ d → ModularForm.heckeU k q ⇑(G d) = ⇑(G (d / q))) ∧
    (¬ q ∣ d → q ∣ L → ModularForm.heckeU k q ⇑(G d) = ModularFormClass.qCoeff g q • ⇑(G d)) ∧
    (¬ q ∣ d → ¬ q ∣ L →
      ModularForm.heckeU k q ⇑(G d) =
        ModularFormClass.qCoeff g q • ⇑(G d) -
          (εL (q : ZMod L) * (q : ℂ) ^ (k - 1)) • ⇑(G (d * q))) := by sorry
