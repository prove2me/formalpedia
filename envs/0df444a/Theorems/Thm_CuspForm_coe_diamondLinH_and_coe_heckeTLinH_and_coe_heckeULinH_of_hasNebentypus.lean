-- Prove2me | Theorems.Thm_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
-- name    : CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/8dd657a2-e60b-5cc6-972d-be652aeaead8
-- title:
--   Action of ⟨ d⟩, T_ℓ, U_q on a nebentypus form
-- statement:
--   Fix a natural number $M$ with $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, a weight $k \in \mathbb{Z}$ and a Dirichlet character $\varepsilon$ of modulus $M$ with values in $\mathbb{C}$. Let $f$ be a cusp form of weight $k$ for the group [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133), the image in $SL(2,\mathbb{Z})$ of the preimage of $H$ under the homomorphism $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$, $\gamma \mapsto \gamma_{11} \bmod M$, and let $g$ be a cusp form of weight $k$ for $\Gamma_1(M)$, with the same underlying function $\mathbb{H} \to \mathbb{C}$ as $f$. Assume $g$ has nebentypus $\varepsilon$ in the sense that $g(\gamma\tau) = \varepsilon(\gamma_{11})\,(\gamma_{10}\tau + \gamma_{11})^{k}\,g(\tau)$ for every $\gamma \in \Gamma_0(M)$ and every $\tau \in \mathbb{H}$. Then three assertions hold, all as identities of functions on $\mathbb{H}$: (i) for every $d \in (\mathbb{Z}/M)^\times$, the diamond operator value $\langle d\rangle f$ given by [`CuspForm.diamondLinH k d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L132) equals $\varepsilon(d) \cdot g$; (ii) for every prime $\ell$ with $\ell \nmid M$, the operator [`CuspForm.heckeTLinH k`](def/CuspForm_HeckeOperatorFormsGammaH.html#L224) applied to $f$ equals $\sum_{j<\ell} g\big|_k \begin{pmatrix}1&j\\0&\ell\end{pmatrix} + \varepsilon(\ell)\cdot \big(g\big|_k \begin{pmatrix}\ell&0\\0&1\end{pmatrix}\big)$; (iii) for every prime $q$ dividing $M$, the operator [`CuspForm.heckeULinH k q`](def/CuspForm_HeckeOperatorFormsGammaH.html#L171) applied to $f$ equals $\sum_{j<q} g\big|_k \begin{pmatrix}1&j\\0&q\end{pmatrix}$. Here the three operators are the linear maps on cusp forms for [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) defined by slashing, respectively by a lift of $d$ to $\Gamma_0(M)$, by the sum of the $U_\ell$-type slashes together with the slash by a lift of $\ell$ times $\mathrm{diag}(\ell,1)$, and by the $U_q$-type slashes, each taken to be the zero map unless the corresponding stability predicate `StableD`, `StableT`, `StableU` holds.
--
--   This is the standard translation of the Hecke operators $\langle d\rangle$, $T_\ell$ ($\ell \nmid M$) and $U_q$ ($q \mid M$) on $S_k(\Gamma_H(M))$ into the nebentypus formalism for forms on $\Gamma_1(M)$, where $T_\ell$ acquires the familiar shape $U_\ell + \varepsilon(\ell)\,(\cdot)\big|_k\mathrm{diag}(\ell,1)$ whose effect on $q$-expansions is $a_n \mapsto a_{\ell n} + \varepsilon(\ell)\ell^{k-1}a_{n/\ell}$. It serves as the bridge between the operator-theoretic constructions on $\Gamma_H$-level cusp forms and the language of primitive forms and eigenvalue conditions, and is used in the construction of eigenform bases and in the analysis of old and new subspaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus.lean

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hfg : (⇑f : UpperHalfPlane → ℂ) = ⇑g) (hg : CuspForm.HasNebentypus ε g) :
    (∀ d : (ZMod M)ˣ, (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) = ε (d : ZMod M) • ⇑g) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      (⇑(CuspForm.heckeTLinH k hℓ hℓM f) : UpperHalfPlane → ℂ) =
        ModularForm.heckeU k ℓ ⇑g + ε (ℓ : ZMod M) • ((⇑g) ∣[k] ModularForm.heckeDiagMatrix ℓ)) ∧
    (∀ (q : ℕ), q.Prime → q ∣ M →
      (⇑(CuspForm.heckeULinH k q f) : UpperHalfPlane → ℂ) = ModularForm.heckeU k q ⇑g) := by sorry
