-- Prove2me | Theorems.Thm_AbelianCayleyHDX_lemma_3_6
-- name    : AbelianCayleyHDX.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:38:02.000018+00:00
-- url     : https://prove2.me/theorems/6c6239c6-b23c-49e3-8a9b-5f6713124256
-- title:
--   Lemma 3.6 — the trace map embeds $A(D)$ into $\ker H_D$; row space distance $\ge 3$
-- statement:
--   Under the standing assumptions of Section 3 ($q = 2^h \ge 8$, $F = \mathbb F_{q^2}$, $t \ge 1$, $D \subseteq \mathrm{PG}(t-1,F)$ spanning), the map
--   $$\Phi : A(D) \to \mathbb F_2^{\Omega}, \qquad \Phi(u)(p, x) = \mathrm{Tr}\big(p\,u(x)\big),$$
--   is an injective $\mathbb F_2$-linear map into $\ker H_D$, so
--   $$\dim_{\mathbb F_2}\ker H_D \ge 2h \dim_F A(D).$$
--   The images under $\Phi$ of the globally affine functions $V_0 \to F$ (the functions $x \mapsto C + a(x)$, $C \in F$, $a \in V_0^\vee$) separate every pair of columns, and for each column one of them is nonzero there. Consequently, the binary row space of $H_D$ has minimum distance at least three.
--
--   Differences from the source:
--   - encoding: $F = \mathbb F_{q^2}$ → any finite field with $q^2$ elements; reason: all such fields are isomorphic to $\mathbb F_{q^2}$
--   - encoding: $q = 2^h \ge 8$ → $h \in \mathbb N$ with $8 \le 2^h$; reason: same parameters
--   - encoding: $\mathrm{Tr} = \mathrm{Tr}_{F/\mathbb F_2}$ → `Algebra.trace (ZMod 2) F` for an $\mathbb F_2$-algebra structure on $F$; reason: the structure exists in characteristic two and is unique
--   - encoding: $\Phi$ is $\mathbb F_2$-linear → $\Phi(u + v) = \Phi(u) + \Phi(v)$; reason: an additive map between $\mathbb F_2$-vector spaces is $\mathbb F_2$-linear
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.6, p.13

import Mathlib
import Definitions.Def_AbelianCayleyHDX_IsSpanning
import Definitions.Def_AbelianCayleyHDX_affineSpace
import Definitions.Def_AbelianCayleyHDX_HD
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_rowspan
import Definitions.Def_AbelianCayleyHDX_MinDistAtLeast3
import Definitions.Def_AbelianCayleyHDX_Phi

namespace AbelianCayleyHDX

/-- **Lemma 3.6** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.6, p.13). Under the standing assumptions of Section 3
(`q = 2^h ≥ 8`, `F = 𝔽_{q²}`, `t ≥ 1`, `D ⊆ PG(t − 1, F)` spanning), the map
`Φ : A(D) → 𝔽₂^Ω`, `Φ(u)(p, x) = Tr(p u(x))`, is an injective `𝔽₂`-linear map into `ker H_D`, so
`dim_{𝔽₂} ker H_D ≥ 2h dim_F A(D)`. The images under `Φ` of the globally affine functions
`V₀ → F` separate every pair of columns, and for each column one of them is nonzero there.
Consequently the binary row space of `H_D` has minimum distance at least three.

**Formalization Note** `Tr = Tr_{F/𝔽₂}` is `Algebra.trace (ZMod 2) F` for the (unique)
`𝔽₂`-algebra structure of `F`. `𝔽₂`-linearity is additivity (an additive map of `𝔽₂`-spaces is
`𝔽₂`-linear). A globally affine function is `x ↦ C + a(x)` with `C ∈ F` and `a ∈ V₀^∨`. -/
theorem lemma_3_6 (h : ℕ) (hq : 8 ≤ 2 ^ h) {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    (hF : Fintype.card F = (2 ^ h) ^ 2) {t : ℕ} (ht : 1 ≤ t) (D : Finset (PG t F))
    (hD : IsSpanning D) :
    (∀ u v : (Fin t → F) → F, Phi (u + v) = Phi u + Phi v) ∧
    (∀ u ∈ affineSpace D, Phi u ∈ kerF2 (HD D)) ∧
    (∀ u ∈ affineSpace D, Phi u = 0 → u = 0) ∧
    2 * h * Module.finrank F (affineSpace D) ≤ Module.finrank (ZMod 2) (kerF2 (HD D)) ∧
    (∀ c c' : Omega F t, c ≠ c' → ∃ (C : F) (a : Module.Dual F (Fin t → F)),
      Phi (fun x => C + a x) c ≠ Phi (fun x => C + a x) c') ∧
    (∀ c : Omega F t, ∃ (C : F) (a : Module.Dual F (Fin t → F)), Phi (fun x => C + a x) c ≠ 0) ∧
    MinDistAtLeast3 (rowspan (HD D)) := by sorry

end AbelianCayleyHDX
