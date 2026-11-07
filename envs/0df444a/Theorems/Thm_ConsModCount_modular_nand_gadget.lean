-- Prove2me | Theorems.Thm_ConsModCount_modular_nand_gadget
-- name    : ConsModCount.modular_nand_gadget
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:29:17.969068+00:00
-- url     : https://prove2.me/theorems/9e48edb9-d9e1-416d-ad37-20b405fd9c59
-- title:
--   Lemma (Unweighted modular NAND gadget) — NAND from $Q_C$ modulo every prime $p\ge7$
-- statement:
--   Let $p\ge7$ be prime and $H$ a finite conservative template on a finite nonempty set $D$ with a Mal'tsev polymorphism. Let $C\subseteq D$ have three elements, $d\in C$, and $c_0\in C\setminus\{d\}$, and suppose $Q_C\in\mathrm{pp}(H)$ (singleton fibre $\{d\}$). Then there is an unweighted $H$-gadget with two ports whose extension counts vanish when a port value lies outside $T=\{c_0,d\}$ and, with $c_0$ labelled $0$ and $d$ labelled $1$, are congruent modulo $p$ on $T\times T$ to
--
--   $$\mathrm{NAND}=\begin{pmatrix}1&1\\1&0\end{pmatrix}.$$
--
--   The gadget reduces the Boolean NAND template to $\#_p\mathrm{CSP}(H)$.
--
--   Differences from the source:
--   - reading: a gadget on Boolean terminals in T = {c0, d} → extension count 0 whenever a terminal value lies outside T; reason: the terminals are restricted to T (proof, p.21: "Restrict two terminals x, y to T")
--   - reading: c0 (an element of the doubled fibre) → every c0 ∈ C \ {d}; reason: the source names either element of the doubled fibre c0
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §12, Lemma (Unweighted modular NAND gadget), p.21 (PDF p.22)

import Definitions.Def_ConsModCount_Balance
import Definitions.Def_ConsModCount_Polymorphism

set_option autoImplicit false

namespace ConsModCount

/-- **Lemma (Unweighted modular NAND gadget)** (Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §12, p.21, PDF p.22). Fix a prime `p ≥ 7`. If a
conservative Mal'tsev template `H` pp-defines some `Q_C`, then there is a fixed unweighted
`H`-gadget on Boolean terminals in `T = {c₀, d}` with `c₀` labelled `0` and `d` labelled `1`, whose
extension counts modulo `p` are `NAND = (1 1; 1 0)`.

**Formalization Note.** `C = {c₀, c₁, d}` with singleton fibre `{d}`; `c₀` is either element of the
doubled fibre. "Terminals in `T`": the extension count is `0` whenever a terminal value lies outside
`T`; on `T × T` it is `1` except at `(d, d)`, where it is `0`, modulo `p`. -/
theorem modular_nand_gadget (p : ℕ) (hp : p.Prime) (h7 : 7 ≤ p) {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (H : Template D) (hH : Conservative H) (hM : HasMaltsev H) (C : Finset D) (d c₀ : D)
    (hC : C.card = 3) (hd : d ∈ C) (hc₀ : c₀ ∈ C) (hne : c₀ ≠ d) (hQ : PPDefinable H (Q C d)) :
    ∃ G : Gadget H 2, ∀ x y : D,
      ((x = c₀ ∨ x = d) → (y = c₀ ∨ y = d) →
        (G.extCount ![x, y] : ZMod p) = if x = d ∧ y = d then 0 else 1) ∧
      (¬ ((x = c₀ ∨ x = d) ∧ (y = c₀ ∨ y = d)) → G.extCount ![x, y] = 0) := by sorry

end ConsModCount
